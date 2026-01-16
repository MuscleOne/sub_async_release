# Sub_Async

> 基于 CPS 的异步计算扩展 (CPS-based async computation extension for Sub language)

扩展自 [PL Zoo](https://github.com/andrejbauer/plzoo) 的 `sub` 语言（by Andrej Bauer）。

---

## 概览

Sub_Async 在 `sub` 语言（eager 求值 + subtyping + records）的基础上，添加了 **基于 continuation 的异步计算**和 **Future 计算图**。

**核心特性**：
- `async e` 语法：创建非阻塞的异步计算
- `Future<T>` 类型：支持协变 subtyping
- **自动依赖追踪**：对 Future 的运算自动创建依赖型 Future（无阻塞 await）
- **自动解析**：依赖完成时级联触发 Future 解析
- 非确定性调度：模拟并发执行环境

---

## 快速开始

### 依赖环境
- OCaml 4.14+
- Dune 3.0+
- Menhir 2.1+

### Ubuntu/Debian 系统配置

```bash
# 安装 opam
sudo apt update && sudo apt install -y opam

# 初始化 opam
opam init -y --disable-sandboxing
eval $(opam env)

# 安装构建工具
opam install -y dune menhir

# 添加到 ~/.bashrc 永久生效
echo 'eval $(opam env)' >> ~/.bashrc
```

### 构建与运行

```bash
# 构建
dune build

# 运行示例
dune exec src/sub_async/sub_async.exe examples/01_basic.sub
```

---

## 核心特性：Future 计算图

### 问题（v1.0）

```ocaml
let x = async (2+3) in
let y = async (10*10) in
x + y  (* ❌ 阻塞：await x，然后 await y，最后返回结果 *)
```

**问题**：即使使用了 `async`，运算符仍会立即 await，无法实现真正的并行。

### 解决方案（v2.0）

```ocaml
let x = async (2+3) in        (* Future 0 *)
let y = async (10*10) in      (* Future 1 *)
x + y                         (* ✅ 立即返回 Future 2: depends on [0, 1] *)
```

**关键创新**：运算符（`+`, `-`, `*`, `/`, `=`, `<`）检测到 Future 时，创建 **Dependent Future** 而非阻塞等待。

### 工作原理

```ocaml
type status =
  | Pending of expr * environment * continuation list
  | Completed of expr
  | Dependent of dependency  (* v2.0 新增 *)

type dependency = {
  depends_on: int list;              (* 依赖列表 *)
  compute: expr list -> expr;        (* 组合函数 *)
  waiters: continuation list;        (* 等待的 continuations *)
}
```

**当 `x + y` 执行时**：
1. `x` 和 `y` 都是 Future？→ 创建 Dependent Future
2. 注册依赖关系：`[id_x; id_y]`
3. 立即返回（非阻塞！）
4. 依赖完成时 → 通过 `check_and_resolve_dependent` 自动解析

---

## 示例程序

| 文件 | 用途 | 关键特性 |
|------|------|---------|
| `00_sub_only.sub` | 基线对比（原版 sub，无 async） | 对比参照 |
| `01_basic.sub` | 基础 async + continuation 自动调用 | 入门演示 |
| `03_fire_and_forget.sub` | 不使用结果的 async 任务 | Fire-and-forget |
| `04_future_graph.sub` | **核心演示**：非阻塞运算符 | v2.0 核心功能 |
| `10_fibonacci.sub` | Fibonacci 数据流 | 链状依赖 |
| `11_diamond_dependency.sub` | Diamond 模式（Fork-Join） | 并行汇聚 |
| `12_mapreduce.sub` | MapReduce 模式 | Map-Reduce 聚合 |
| `13_pipeline.sub` | Pipeline 流水线模式 | 级联处理 |

### 核心演示：非阻塞运算符

**文件**：`examples/04_future_graph.sub`

```ocaml
let x = async (2 + 3) in       # Future 0
let y = async (10 * 10) in     # Future 1
let z = async (7 * 8) in       # Future 2
let sum = x + y + z in         # Future 3,4 (立即返回！)
3 + 1                          # 返回 4，不等待！
```

**输出**：
```
[dependent] Future #3 depends on [0; 1]
[dependent] Future #4 depends on [3; 2]
[main] Final result obtained        ← 在 futures 完成前！
- : int = 4                         ← 3+1 的结果
```

**证明**：`3 + 1` 在异步任务完成前就执行了 — 真正的非阻塞行为！

---

## 经典并发模式

我们的空间/时间解耦设计天然支持经典并发算法：

### 🔷 Diamond 模式（Fork-Join）

```
      fetch_user
       /      \
  validate  check_quota  ← 并行执行（空间解耦）
       \      /
    create_order         ← 自动等待（时间解耦）
```

**示例**：`examples/11_diamond_dependency.sub`

### 🗺️ MapReduce 模式

```
map1  map2  map3  map4   ← 并行任务
   \    |    |   /
      reduce           ← 自动聚合
```

**示例**：`examples/12_mapreduce.sub`（经5次运行验证随机调度）

### 🌊 Pipeline 流水线

```
fetch → transform → validate → save  ← 自动级联
```

**示例**：`examples/13_pipeline.sub`

### 🔢 Fibonacci 数据流

链状依赖的自动级联解析。

**示例**：`examples/10_fibonacci.sub`

---

## 设计理念

### 空间解耦 (Space Decoupling)
`async e` 不指定**谁**执行任务 — 进入全局队列，由 Scheduler 随机选择。

### 时间解耦 (Time Decoupling)
`async` 立即返回；任务异步执行。完成时，自动调用已注册的 continuations。

### DAG by Design
Future 计算图构造上就是 **DAG（有向无环图）**：
- Let 绑定强制顺序（无前向引用）
- 静态作用域阻止循环
- 不可变 Future 创建后无法修改

**结果**：理论上不可能产生环 — 实践中无需环检测（虽然实现了防御性检查）。

---

## 实现要点

- **Scheduler**：非确定性（从 ready queue 随机选择任务）
- **ContinuationStore**：管理 Future 状态和自动通知
- **Dependent Future 解析**：`check_and_resolve_dependent` 触发级联解析
- **类型系统**：协变 `Future<T>` subtyping

**核心代码量**：约286行（原版 sub 约150行）

---

## 与原版 sub 对比

| 特性 | sub | sub_async |
|---------|-----|-----------|
| 求值策略 | Eager | Eager + CPS |
| 异步支持 | 无 | `async e` |
| Future 类型 | 无 | `Future<T>` |
| 依赖追踪 | 无 | 自动 |

---

## 致谢

- **PL Zoo** by Andrej Bauer — 框架和原版 `sub` 语言
- **Supervisor 的指导** — 空间/时间解耦设计的启发
