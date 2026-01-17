# 设计决策与权衡

本文档记录 Sub_Async 中重要的设计决策、遇到的冲突以及做出的权衡。

---

## 1. 布尔运算符与短路求值

### 问题描述

**短路求值（Short-Circuit Evaluation）** 是布尔运算符的传统语义：

```ocaml
false && x  →  false    (* 不求值 x *)
true  || x  →  true     (* 不求值 x *)
```

这与 Future 的"自动并行化"产生根本冲突。

### 冲突场景

**场景 1：已启动的 Future**
```ocaml
let x = async (expensive_computation()) in  (* Future 已在后台运行 *)
false && x  (* 期望短路：不使用 x 的结果 *)
```

问题：
- `async` 已启动计算，`x` 的副作用可能已发生
- 短路语义要求"不求值 x"，但 Future 已经在算了
- 如何协调？取消任务（需要取消机制）？忽略结果（资源浪费）？

**场景 2：并行计算破坏短路**
```ocaml
let x = async (true) in
let y = async (false) in
x && y  (* 如果 lift 成 Future<bool> *)
```

传统短路：先求值 `x`，如果 `false` 则不求值 `y`  
Future lift：立即返回 `Future #2 (depends_on [0,1])`，`x` 和 `y` 并行计算

**两者互斥**：短路要求"条件性求值"，Future 要求"立即并行"。

### 设计选项对比

| 选项 | 语义 | 优点 | 缺点 |
|------|------|------|------|
| **选项 A：完全 lift** | `Future<bool> && Future<bool> → Future<bool>` | 最大化并行 | 违反短路，浪费计算 |
| **选项 B：顺序等待** | 先 await 左操作数，再决定右操作数 | 保持短路语义 | 破坏并行性，与哲学冲突 |
| **选项 C：禁止 Future** | 布尔运算符不接受 `Future<bool>` | 避免冲突，保持短路 | 不一致（比较运算支持） |

### 当前实现（选项 C）

**类型检查器**（[type_check.ml](../src/sub_async/type_check.ml) 第 50-52 行）：
```ocaml
| And (e1, e2)
| Or (e1, e2) -> check ctx e1 TBool; check ctx e2 TBool; TBool
| Not e -> check ctx e TBool; TBool
```
- 要求操作数必须是 `TBool`
- 拒绝 `Future<bool>` 操作数
- 返回类型总是 `TBool`

**求值器**（[eval.ml](../src/sub_async/eval.ml) 第 177-189 行）：
```ocaml
| And (e1, e2) ->
    eval_cps env e1 (fun v1 ->
      eval_cps env e2 (fun v2 ->         (* 总是求值 e2 *)
        value_to_bool v1 (fun b1 ->
          value_to_bool v2 (fun b2 ->    (* 隐式 await *)
            k (Bool (b1 && b2))))))
```
- 实际上总是求值两个操作数（CPS 特性）
- 如果遇到 Future，通过 `value_to_bool` 隐式 await
- 但类型检查器已阻止 Future 传入

### 不一致性

**比较运算符支持 Future**：
```ocaml
(* type_check.ml 第 46-49 行 *)
| Equal (e1, e2)
| Less (e1, e2) ->
    (match type_of ctx e1, type_of ctx e2 with
     | TFuture TInt, TInt | TInt, TFuture TInt | TFuture TInt, TFuture TInt 
         -> TFuture TBool    (* ✅ 返回 Future<bool> *)
     | TInt, TInt -> TBool
     | _ -> type_error ...)
```

**问题**：比较运算可以产生 `Future<bool>`，但布尔运算无法使用它

```ocaml
(* 这段代码被类型系统拒绝 *)
let x = async (10) in
let y = async (20) in
let cmp = x < y in         (* cmp : Future<bool> *)
cmp && true                (* ❌ Type error *)
```

### 未来方向

**选项 1：完全 lift（激进）**
- 实现 `binary_bool_op_*` 模板（类似算术运算）
- 文档明确："短路在 Future 上不适用"
- 用户如需短路，使用 `if` 表达式

**选项 2：回退比较运算（保守）**
- 修改 `Equal`/`Less` 不返回 `Future<bool>`
- 强制在比较前 await Future
- 保持所有运算符的短路语义

**选项 3：引入严格模式运算符**
- `&&` 保持短路，不支持 Future
- 新增 `&&&` 严格求值，支持 Future
- 类似 Haskell 的 `&&` vs `Monad (>>=)`

---

## 2. 引用计数 vs 追踪式 GC

### 设计选择

**当前实现**：引用计数（Reference Counting）

**理由**：
1. **确定性回收**：Future 完成后立即释放（无需 GC 线程）
2. **DAG 保证**：Let + 静态作用域保证无环，引用计数适用
3. **可预测性**：适合教学和形式验证

**代码**（[future.ml](../src/sub_async/future.ml) 第 49-66 行）：
```ocaml
let rec decr_ref id =
  match ref_counts[id] with
  | 1 -> 
      List.iter decr_ref (get_deps id);  (* 级联释放 *)
      Hashtbl.remove table id;
      Hashtbl.remove ref_counts id
  | n -> ref_counts[id] <- n-1
```

**局限性**：
- 无法处理循环引用（但理论上不可能）
- 引用计数操作有开销（每次创建/使用都要更新）

**替代方案**：
- Mark-and-Sweep：需要 GC 线程，stop-the-world
- 分代 GC：复杂度高，不适合小型语言

---

## 3. CPS 求值器 vs 直接风格

### 设计选择

**当前实现**：Continuation-Passing Style (CPS)

**理由**：
1. **天然支持异步**：continuation 就是回调函数
2. **避免 callback hell**：CPS 变换在后端完成
3. **统一控制流**：`await` 不需要特殊处理

**代码对比**：

**直接风格（无法处理异步）**：
```ocaml
let rec eval env = function
  | Plus (e1, e2) ->
      let v1 = eval env e1 in    (* 阻塞 *)
      let v2 = eval env e2 in
      Int (v1 + v2)
```

**CPS 风格（支持异步）**：
```ocaml
let rec eval_cps env e k = match e with
  | Plus (e1, e2) ->
      eval_cps env e1 (fun v1 ->
        eval_cps env e2 (fun v2 ->
          k (Int (v1 + v2))))
```

**局限性**：
- 调用栈深度（OCaml 无尾调用优化保证）
- 调试困难（栈帧包含大量 continuation）

---

## 4. 非确定性调度 vs 确定性

### 设计选择

**当前实现**：非确定性（随机调度）

**理由**：
1. **模拟并发**：单线程环境下展示并发效果
2. **测试健壮性**：暴露依赖顺序相关的 bug
3. **教学价值**：演示调度的不可预测性

**代码**（[scheduler.ml](../src/sub_async/scheduler.ml) 第 21-41 行）：
```ocaml
let run_one_random () =
  if not (Queue.is_empty queue) then begin
    let idx = Random.int (Queue.length queue) in
    (* 随机选择一个任务执行 *)
    ...
  end
```

**局限性**：
- 不可重现（每次运行顺序不同）
- 性能不优（需要转换队列为列表）
- 无优先级控制

**替代方案**：
- FIFO 调度：确定性，但失去并发感
- 优先级队列：需要用户指定优先级
- Work-stealing：真正的多线程实现

---

## 5. 静态依赖图 vs 动态依赖

### 设计选择

**当前实现**：静态依赖图（编译时确定结构）

**限制**：
```ocaml
(* ❌ 无法表达：后续计算依赖前面的值 *)
let x = async f() in
let y = async (g x) in  (* g 需要 x 的值，必须 await *)
x + y
```

**对比 Monad**：
```haskell
do
  x <- async f
  y <- async (g x)  -- ✅ Monad 的 >>= 可以表达动态依赖
  return (x + y)
```

**设计理由**：
- 牺牲表达能力，换取运算符的自动并行化
- 静态依赖图更适合编译优化
- 类型系统更简单（无需 Monad 类型类）

**与 Applicative Functor 的关系**：
```haskell
(+) <$> async f <*> async g  -- 类似我们的 Future lift
```
我们的方案接近 Applicative，而非完整的 Monad。

---

## 6. 协变 Subtyping

### 设计选择

`Future<T>` 对类型参数 `T` 协变：

```ocaml
(* type_check.ml 第 96-99 行 *)
let rec subtype ty1 ty2 = match ty1, ty2 with
  | TFuture t1, TFuture t2 -> subtype t1 t2  (* 协变 *)
  | ty1, ty2 -> ty1 = ty2
```

**含义**：
```ocaml
subtype TInt (TFuture TInt)         (* ✅ int 是 Future<int> 的子类型 *)
subtype (TFuture TInt) TInt         (* ❌ 反向不成立 *)
```

**理由**：
- 值可以自动提升为 Future（`async (n)` 隐式转换）
- 符合"async 只是延迟计算"的直觉

**局限性**：
- 不安全的协变（如果 Future 可变，会破坏类型安全）
- 当前实现中 Future 不可变，所以安全

---

## 总结

这些设计决策形成了 Sub_Async 的核心哲学：

1. **自动化优于控制**（牺牲短路，获得并行）
2. **隐式优于显式**（运算符自动 lift，无需手动管理）
3. **简单优于通用**（静态依赖图，非完整 Monad）
4. **确定性优于性能**（引用计数 GC，非追踪式）

每个选择都是在**表达能力**、**自动化程度**、**实现复杂度**之间的权衡。
