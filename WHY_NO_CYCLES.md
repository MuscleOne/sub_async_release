# 为什么 Future 计算图不会有环？

## 理论保证

### 1. Let 绑定的顺序性

在 sub_async 中，let 绑定是**严格顺序**的：

```ocaml
let x = ... in
let y = ... in  (* y 可以引用 x *)
let z = ... in  (* z 可以引用 x 和 y *)
...
```

**规则**：变量只能引用**已经定义**的变量。

### 2. 静态作用域

编译时检查确保：
- ❌ 不能前向引用（forward reference）
- ❌ 不能自引用（self-reference）
- ❌ 不能循环引用（circular reference）

```ocaml
(* 这些都会在编译时报错 *)
let x = y + 1 in  (* Error: y not defined yet *)
let y = x + 1 in
x

let x = x + 1 in  (* Error: x used in its own definition *)
x
```

### 3. 不可变绑定

一旦创建，Future 不能被修改：

```ocaml
let x = async (10) in
(* 不能做: x := async (20) *)
(* 不能做: x.update(...) *)
```

## DAG vs 环

### ✅ 允许：DAG（有向无环图）

```
Future 0
  ↓  ↘
  ↓   Future 1
  ↓     ↓
  ↓   Future 2
  ↓     ↓
  ↘   ↙
Future 3  ← 有两个依赖 [2, 0]，但不是环！
```

**代码**：
```ocaml
let a = async (10) in        # Future 0
let b = a + 1 in             # Future 1: depends on [0]
let c = b + 1 in             # Future 2: depends on [1]
let d = c + a in             # Future 3: depends on [2, 0]
d
```

这是**DAG**，不是环！Future 3 依赖 Future 0 和 Future 2，但：
- Future 0 **不依赖** Future 3
- 没有回边（back edge）

### ❌ 不可能：环

```
Future 0 → Future 1 → Future 2
   ↑                      ↓
   └──────────────────────┘
   (这需要 Future 0 依赖 Future 2，不可能！)
```

要创建这个环，需要：

```ocaml
let x = async (10) in        # Future 0
let y = x + 1 in             # Future 1: depends on [0]
let z = y + 1 in             # Future 2: depends on [1]
let x = z + 1 in             # ❌ Error: x already defined!
```

或者：

```ocaml
let x = z + 1 in             # ❌ Error: z not defined yet!
let y = x + 1 in
let z = y + 1 in
```

## 实现中的防御性检查

虽然理论上不可能，我们仍然添加了 `has_cycle` 检查：

```ocaml
let has_cycle depends_on new_id =
  let rec check_path visited current_id =
    if List.mem current_id visited then
      true  (* Found a cycle! *)
    else
      match Hashtbl.find_opt table current_id with
      | Some (Dependent dep) ->
          List.exists (check_path (current_id :: visited)) dep.depends_on
      | _ -> false
  in
  List.exists (check_path [new_id]) depends_on
```

**作用**：
1. 防御性编程（defensive programming）
2. 捕获潜在的实现 bug
3. 文档化设计意图

**预期**：这个检查永远不会触发（除非实现有 bug）。

## 与递归函数的关系

**问题**：递归函数会创建环吗？

```ocaml
let rec fib = fun f(n: int): int is
  if n < 2 then n
  else fib(n-1) + fib(n-2)
in
let x = async (fib 10) in
x
```

**答案**：❌ 不会！

- `fib` 是**函数**，不是 Future
- `async (fib 10)` 创建 Future 0
- 没有其他 Future 依赖 Future 0，所以没有图
- `fib` 的递归是**值级别**的，不是 Future 级别的

## 类比

### JavaScript Promise

```javascript
const a = Promise.resolve(10);
const b = a.then(x => x + 1);
const c = b.then(x => x + 1);
const d = Promise.all([c, a]).then(([x, y]) => x + y);
```

这也是 DAG，不是环！

### Scala Future

```scala
val a = Future { 10 }
val b = a.map(_ + 1)
val c = b.map(_ + 1)
val d = for {
  x <- c
  y <- a
} yield x + y
```

同样是 DAG！

## 总结

**为什么不会有环？**

1. ✅ **语言设计**：Let 绑定顺序性
2. ✅ **静态检查**：编译时保证无前向引用
3. ✅ **不可变性**：Future 创建后不能修改

**结论**：Sub_Async 的 Future 计算图天然是 **DAG（有向无环图）**，不可能产生环！

**防御性检查**：虽然理论上不可能，但我们仍然添加了环检测，作为防御性编程和文档化设计意图。
