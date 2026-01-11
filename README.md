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

### 构建 (Build)
```bash
dune build
```

### 运行示例 (Run Examples)
```bash
# 原版 sub（无 async）
./_build/default/src/sub/sub.exe examples/00_sub_only.sub

# 基础 async 演示
./_build/default/src/sub_async/sub_async.exe examples/01_basic.sub

# 非确定性调度
./_build/default/src/sub_async/sub_async.exe examples/02_nondeterministic.sub

# Fire-and-forget 模式
./_build/default/src/sub_async/sub_async.exe examples/03_fire_and_forget.sub
```

---

## 核心机制 (Core Mechanism)

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
- ✅ **非阻塞**：`async` 立即返回 `Future id`，不等待任务完成
- ✅ **隐式等待**：使用 future 值时调用 `ContinuationStore.await`，注册 continuation
- ✅ **自动通知**：任务完成时调用 `ContinuationStore.complete`，执行 `List.iter (fun k -> k v) ks`

### ContinuationStore 模块

管理 futures 和它们的 continuations：[src/sub_async/eval.ml 第57-126行](src/sub_async/eval.ml#L57-L126)

```ocaml
module ContinuationStore = struct
  type status =
    | Pending of expr * environment * continuation list
    | Completed of expr

  (* 创建 future - 第88-102行 *)
  val create : expr -> environment -> int
  
  (* 注册 continuation - 第105-113行 *)
  val await : int -> continuation -> unit
  
  (* 完成并通知 - 第78-86行 *)
  val complete : int -> expr -> unit
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

**实现位置**：[src/sub_async/eval.ml 第257-260行](src/sub_async/eval.ml#L257-L260) → `ContinuationStore.create`

### 时间解耦 (Time Decoupling)  
`create` 立即返回 future ID；任务异步执行。**任务完成时，`complete` 函数 call 所有注册的 continuations**。

**实现位置**：
- 任务调度：[eval.ml 第88-102行](src/sub_async/eval.ml#L88-L102) → `Scheduler.schedule`
- 自动通知：[eval.ml 第78-86行](src/sub_async/eval.ml#L78-L86) → `List.iter (fun k -> k v) ks`

### 关键条件 (Key Condition)
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

### 01_basic.sub
基础演示 continuation auto-call：
```ocaml
let x = async (2 + 3) in
let y = async (10 * 10) in  
let z = async (7 * 8) in
x + y + z
(* 结果: 161 *)
```

### 02_nondeterministic.sub
非确定性调度 — 多次运行观察不同执行顺序。

### 03_fire_and_forget.sub
创建 async 任务但不使用结果 — 不会调用 continuations。

---

## 与原版 `sub` 的对比

| 特性 | sub | sub_async |
|---------|-----|-----------|
| 求值策略 | Eager | Eager + CPS |
| 异步支持 | ❌ | ✅ `async e` |
| Future 类型 | ❌ | ✅ `Future<T>` |
| 核心代码 | ~150 行 | ~286 行 |

**新增关键字**：`async`（定义在 [lexer.mll 第14行](src/sub_async/lexer.mll#L14) 和 [parser.mly 第14行](src/sub_async/parser.mly#L14)）

---

## 致谢 (Acknowledgments)

- **PL Zoo** by Andrej Bauer — 框架和原版 `sub` 语言
- **Supervisor 的想法** — 空间/时间解耦的异步计算设计
