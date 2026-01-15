# Sub_Async

> 基于 CPS 的异步计算扩展（Continuation-based async extension for Sub language）

基于 [PL Zoo](https://github.com/andrejbauer/plzoo) 的 `sub` 语言（by Andrej Bauer）。

---

## 概览 (Overview)

本项目扩展了 `sub` 语言（eager 求值 + subtyping + records），添加了 **基于 continuation 的异步计算**。

**核心特性 (Key Features)**:
- `async e` 语法：创建异步计算
- `Future<T>` 类型：协变 subtyping
- Continuation Auto-Call 机制：无需显式 scheduler 轮询
- 非确定性调度 (Non-deterministic scheduling)：模拟并发环境

---

## 项目结构 (Project Structure)

```
sub_async/
├── src/
│   ├── zoo/          # PL Zoo 框架（解释器基础设施）
│   ├── sub/          # 原版 sub 语言（对比基线）
│   └── sub_async/    # 异步扩展（本项目核心）
├── examples/         # 示例程序
└── README.md
```

---

## 构建与运行 (Build & Run)

### 依赖 (Prerequisites)
- OCaml 4.14+
- Dune 3.0+
- Menhir 2.1+

### 环境配置 (Setup)

#### Ubuntu/Debian 系统

1. **安装 opam（OCaml 包管理器）**：
   ```bash
   sudo apt update
   sudo apt install -y opam
   ```

2. **初始化 opam 环境**：
   ```bash
   opam init -y --disable-sandboxing
   eval $(opam env)
   ```

3. **安装构建工具**：
   ```bash
   opam install -y dune menhir
   ```

4. **配置环境变量**（添加到 `~/.bashrc` 或 `~/.profile`）：
   ```bash
   echo 'eval $(opam env)' >> ~/.bashrc
   source ~/.bashrc
   ```

#### macOS 系统

1. **安装 opam（使用 Homebrew）**：
   ```bash
   brew install opam
   ```

2. **初始化 opam 并安装工具**：
   ```bash
   opam init -y
   eval $(opam env)
   opam install -y dune menhir
   ```

#### 验证安装

```bash
ocaml -version    # 应显示 4.14.x 或更高
dune --version    # 应显示 3.0 或更高
menhir --version  # 应显示 20xx 版本
```

### 构建 (Build)
```bash
dune build
```

### 运行示例 (Run Examples)

**推荐顺序**：
```bash
# 1. 原版 sub（无 async，对比基线）
./_build/default/src/sub/sub.exe examples/00_sub_only.sub
# 输出: - : int = 25

# 2. 基础 async 演示（推荐从这个开始）
./_build/default/src/sub_async/sub_async.exe examples/01_basic.sub
# 输出: 161（观察日志中的 continuation 调用）

# 3. 非确定性调度（多次运行观察不同顺序）
./_build/default/src/sub_async/sub_async.exe examples/02_nondeterministic.sub

# 4. Fire-and-forget 模式（观察无 continuation 调用）
./_build/default/src/sub_async/sub_async.exe examples/03_fire_and_forget.sub
# 输出: 42（注意日志里没有 "calling continuations"）

# 5. 🎯 Future 计算图核心演示（v2.0 新增）
./_build/default/src/sub_async/sub_async.exe examples/04_future_graph.sub
# 输出: 4（证明 "3+1" 先于 "x+y+z" 执行！）
# 关键观察: [main] Final result obtained 出现在 futures 完成之前
```

---

## 核心机制 (Core Mechanism)

### 🆕 Future 计算图 (Future Computation Graph) - v2.0

**重大改进**：运算符 (`+`, `-`, `*`, `/`, `=`, `<`) 现在支持 **惰性依赖**！

#### Before (v1.0 - 阻塞式 await)
```ocaml
let x = async (2+3) in        (* Future 0 *)
let y = async (10*10) in      (* Future 1 *)
x + y                         (* ❌ 阻塞：await x, 然后 await y, 最后返回结果 *)
```

**问题**：即使使用 `async`，运算符仍然会 **立即 await**，无法实现真正的并行。

#### After (v2.0 - 依赖型 Future)
```ocaml
let x = async (2+3) in        (* Future 0 *)
let y = async (10*10) in      (* Future 1 *)
x + y                         (* ✅ 立即返回 Future 2: depends on [0, 1] *)
```

**关键改变**：
1. **Plus/Minus/Times/Divide/Equal/Less** 检测操作数是否为 Future
2. 如果是，创建 **Dependent Future** 而不是 await
3. 依赖完成时，**自动解析**下游 Future

#### 实现细节

**Dependent Future 状态** ([eval.ml 第58-64行](src/sub_async/eval.ml#L58-L64)):
```ocaml
type dependency = {
  depends_on: int list;              (* 依赖的 Future IDs *)
  compute: expr list -> expr;        (* 如何组合结果 *)
  waiters: continuation list;        (* 等待这个 Future 的 continuations *)
}

type status =
  | Pending of expr * environment * continuation list
  | Completed of expr
  | Dependent of dependency          (* 👈 NEW *)
```

**Plus 运算符的改写** ([eval.ml 第265-291行](src/sub_async/eval.ml#L265-L291)):
```ocaml
| Plus (e1, e2) ->
    eval_cps env e1 (fun v1 ->
      eval_cps env e2 (fun v2 ->
        match v1, v2 with
        | Future id1, Future id2 ->
            (* 创建依赖型 Future *)
            let new_id = create_dependent_future [id1; id2]
              (fun [v1; v2] -> Int (extract_int v1 + extract_int v2))
            in
            k (Future new_id)  (* 👈 立即返回！ *)
        
        | Future id, Int n | Int n, Future id ->
            let new_id = create_dependent_future [id]
              (fun [v] -> Int (extract_int v + n))
            in
            k (Future new_id)
        
        | Int n1, Int n2 -> k (Int (n1 + n2))
```

**依赖解析** ([eval.ml 第98-113行](src/sub_async/eval.ml#L98-L113)):
```ocaml
let rec check_and_resolve_dependent id =
  match Hashtbl.find_opt table id with
  | Some (Dependent dep) ->
      let all_completed, values = check_dependencies dep.depends_on in
      if all_completed then begin
        let result = dep.compute values in
        Hashtbl.replace table id (Completed result);
        List.iter (fun k -> k result) dep.waiters  (* 通知等待者 *)
      end
```

#### 效果演示

**嵌套依赖**（examples/04_future_graph.sub）:
```ocaml
let x = async (2+3) in           (* Future 0 *)
let y = async (10*10) in         (* Future 1 *)
let z = async (7*8) in           (* Future 2 *)
x + y + z                        (* Future 3 depends on [0,1]
                                    Future 4 depends on [3,2] *)
```

**执行日志**:
```
[async] Created future #0, #1, #2
[dependent] Future #3 depends on [0; 1]
[dependent] Future #4 depends on [3; 2]
[main] Result is Future #4, awaiting...
[🎲 running] Futures execute in random order...
[dependent] Future #3 resolved   ← 自动触发！
[dependent] Future #4 resolved   ← 级联触发！
- : int = 161
```

**关键优势**：
- ✅ **真正的非阻塞**：运算符立即返回，不等待
- ✅ **自动依赖追踪**：编译器级别的计算图
- ✅ **级联解析**：Future A 完成 → Future B 自动检查 → Future C 自动触发
- ✅ **最大化并发**：所有独立任务并行执行

**对比 JavaScript**:
```javascript
// JavaScript Promise
Promise.all([fetch("api1"), fetch("api2")])
  .then(([x, y]) => x + y)

// Sub_Async v2.0
let x = async fetch("api1") in
let y = async fetch("api2") in
x + y  (* 自动创建依赖！ *)
```

---

### `async e` 语法

```ocaml
let x = async (2 + 3) in    (* 创建 future #0，立即返回 *)
x + 10                      (* 使用 x 时注册 continuation *)
```

**实现入口 (Implementation Entry)**：[src/sub_async/eval.ml 第257-260行](src/sub_async/eval.ml#L257-L260)

```ocaml
| Async e' ->
    let id = ContinuationStore.create e' env in
    k (Future id)
```

**行为 (Behavior)**：
- **非阻塞**：`async` 立即返回 `Future id`，不等待任务完成
- **隐式等待**：使用 future 值时调用 `ContinuationStore.await`，注册 continuation
- **自动通知**：任务完成时调用 `ContinuationStore.complete`，执行 `List.iter (fun k -> k v) ks`

### ContinuationStore 模块

管理 futures 和它们的 continuations：[src/sub_async/eval.ml 第57-126行](src/sub_async/eval.ml#L57-L126)

```ocaml
module ContinuationStore = struct
  type status =
    | Pending of expr * environment * continuation list
    | Completed of expr

  val create : expr -> environment -> int       (* 第88-102行 *)
  val await : int -> continuation -> unit       (* 第105-113行 *)
  val complete : int -> expr -> unit            (* 第78-86行 *)
end
```

**工作流程 (Workflow)**：
1. **创建阶段**：`create` 产生 future ID，任务进入 `Scheduler.queue`
2. **使用阶段**：`await` 注册 continuation 到 `ks` 列表（非阻塞）
3. **完成阶段**：`complete` 执行 `List.iter (fun k -> k v) ks`

### 类型系统 (Type System)

**类型规则**：
```
Γ ⊢ e : T
─────────────────────
Γ ⊢ async e : Future T
```

**协变性 (Covariance)**：[src/sub_async/type_check.ml 第99-101行](src/sub_async/type_check.ml#L99-L101)
```ocaml
| TFuture ty1', TFuture ty2' ->
    subtype ty1' ty2'  (* T1 <: T2 ⇒ Future T1 <: Future T2 *)
```

---

## 设计理念 (Design Philosophy)

### 空间解耦 (Space Decoupling)
`async e` 不指定谁来执行任务 — 进入全局队列，由 Scheduler 随机选择。

**代码位置**：[eval.ml 第257-260行](src/sub_async/eval.ml#L257-L260) → `ContinuationStore.create`

### 时间解耦 (Time Decoupling)  
`create` 立即返回 future ID；任务异步执行。任务完成时，`complete` 函数 call 所有注册的 continuations。

**代码位置**：
- 任务调度：[eval.ml 第88-102行](src/sub_async/eval.ml#L88-L102) → `Scheduler.schedule`
- 自动通知：[eval.ml 第78-86行](src/sub_async/eval.ml#L78-L86) → `List.iter (fun k -> k v) ks`

**关键条件**：
- `ks = []`（无等待者）→ `complete` 不调用任何 continuation（fire-and-forget）
- `ks ≠ []`（有等待者）→ `complete` 调用所有 continuations

---

## 示例说明 (Examples)

| 文件 | 用途 |
|------|------|
| `00_sub_only.sub` | 原版 sub 语言（对比基线，无 async） |
| `01_basic.sub` | 基础 async + continuation auto-call |
| `02_nondeterministic.sub` | 非确定性调度（多次运行观察） |
| `03_fire_and_forget.sub` | 不使用结果的 async（`ks = []`） |
| `04_future_graph.sub` | **核心演示**：Future 计算图 (v2.0) |

### 01_basic.sub
基础演示 continuation auto-call：
```ocaml
let x = async (2 + 3) in
let y = async (10 * 10) in  
let z = async (7 * 8) in
x + y + z
(* 结果: 161 *)
```

### 04_future_graph.sub ⭐
**v2.0 核心演示**：证明 `3 + 1` 可以在 `x + y + z` 完成前执行！

```ocaml
let x = async (2 + 3) in           # Future 0
let y = async (10 * 10) in         # Future 1
let z = async (7 * 8) in           # Future 2
let sum = x + y + z in             # Future 3,4 (立即返回！)
3 + 1                              # ← 立即执行，返回 4
```

**执行证据**:
```
[dependent] Future #3 depends on [0; 1]
[dependent] Future #4 depends on [3; 2]
[main] Final result obtained        ← 在 futures 完成前！
...
- : int = 4                         ← 3+1 的结果！
```

**关键点**：
- ❌ v1.0：`x + y + z` 会 await 所有 futures（阻塞）
- ✅ v2.0：`x + y + z` 创建 Dependent Future（非阻塞）
- ✅ 结果：`3 + 1` 立即执行，不等待异步任务完成！

### 02_nondeterministic.sub
非确定性调度 — 多次运行观察不同执行顺序。

### 03_fire_and_forget.sub
创建 async 任务但不使用结果 — 不会调用 continuations。

---

## 与原版 `sub` 的对比

| 特性 | sub | sub_async |
|---------|-----|-----------|
| 求值策略 | Eager | Eager + CPS |
| 异步支持 | 无 | `async e` |
| Future 类型 | 无 | `Future<T>` |
| 核心代码 | ~150 行 | ~286 行 |

**新增关键字**：`async`（定义在 [lexer.mll 第14行](src/sub_async/lexer.mll#L14) 和 [parser.mly 第14行](src/sub_async/parser.mly#L14)）

---

## 致谢 (Acknowledgments)

- **PL Zoo** by Andrej Bauer — 框架和原版 `sub` 语言
- **Supervisor 的想法** — 空间/时间解耦的异步计算设计
