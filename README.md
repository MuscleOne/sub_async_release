# Sub_Async

> 基于 CPS 的异步计算扩展

扩展自 [PL Zoo](https://github.com/andrejbauer/plzoo) 的 `sub` 语言（by Andrej Bauer）。

---

## 概览

Sub_Async 在 `sub` 语言基础上添加了基于 continuation 的异步计算和 Future 计算图。

**特性**：
- `async e` 语法：创建异步计算
- `Future<T>` 类型：协变 subtyping
- 自动依赖追踪：运算符对 Future 创建依赖而非阻塞
- 自动解析：依赖完成时级联触发
- 非确定性调度：模拟并发环境

---

## 快速开始

### Ubuntu/Debian 系统配置

```bash
# 安装 opam
sudo apt update && sudo apt install -y opam

# 初始化 opam
opam init -y --disable-sandboxing
eval $(opam env)

# 安装构建工具
opam install -y dune menhir

# 添加到 ~/.bashrc
echo 'eval $(opam env)' >> ~/.bashrc
```

### 构建与运行

```bash
dune build
dune exec src/sub_async/sub_async.exe examples/01_basic.sub
```

---

## Future 计算图

### v1.0 的问题

```ocaml
let x = async (2+3) in
let y = async (10*10) in
x + y  (* 阻塞：await x, await y, 返回结果 *)
```

运算符立即 await，无法并行。

### v2.0 解决方案

```ocaml
let x = async (2+3) in        (* Future 0 *)
let y = async (10*10) in      (* Future 1 *)
x + y                         (* 立即返回 Future 2: depends on [0, 1] *)
```

运算符检测 Future 后创建 Dependent Future。

### 实现

```ocaml
type status =
  | Pending of expr * environment * continuation list
  | Completed of expr
  | Dependent of dependency

type dependency = {
  depends_on: int list;
  compute: expr list -> expr;
  waiters: continuation list;
}
```

执行 `x + y` 时：
1. 检测两个操作数都是 Future
2. 注册依赖 `[id_x; id_y]`
3. 立即返回新 Future
4. 依赖完成时自动解析

---

## 设计理念

### 空间解耦 (Space Decoupling)

**传统 OOP 方式**：
```python
obj.method(arg)      # 必须指定 obj
thread1.submit(task) # 必须指定 thread1
executor.execute(f)  # 必须指定 executor
```

**Sub_Async 方式**：
```ocaml
async (2 + 3)  (* 只说"做什么"，不说"谁来做" *)
```

`async` 语义就是"丢出去"：
- 任务进入全局队列
- Scheduler 随机选择执行
- 不绑定执行者身份/位置/线程

**核心**：解耦任务定义与执行空间。

### 时间解耦 (Time Decoupling)

`async` 立即返回 Future，主程序需要结果时注册 continuation，任务完成后调用已注册的 continuations。

**流程**：
```ocaml
let x = async (compute()) in  (* 1. 立即返回 Future 0 *)
(* ... 主程序继续执行 ... *)
x + 1                         (* 2. 使用 x 时注册 continuation *)
                              (* 3. Future 0 完成后调用 continuation *)
```

**对比同步**：
```ocaml
let x = compute() in  (* 阻塞等待 *)
x + 1
```

**核心**：解耦任务发起与结果获取，主程序决定何时需要结果。

### DAG by Design
- Let 绑定强制顺序
- 静态作用域阻止循环
- Future 不可变

理论上不可能产生环。

---

## 示例

| 文件 | 说明 |
|------|------|
| `00_sub_only.sub` | 原版 sub（无 async） |
| `01_basic.sub` | 基础用法 |
| `03_fire_and_forget.sub` | Fire-and-forget 模式 |
| `04_future_graph.sub` | 非阻塞运算符 |
| `10_fibonacci.sub` | Fibonacci 数据流 |
| `11_diamond_dependency.sub` | Diamond（Fork-Join） |
| `12_mapreduce.sub` | MapReduce |
| `13_pipeline.sub` | Pipeline 流水线 |

详见各文件内注释。

---

## 实现

**核心模块**：

- **Scheduler**：非确定性调度
  - [`schedule`](src/sub_async/eval.ml#L22)：任务入队
  - [`run_one_random`](src/sub_async/eval.ml#L32-L50)：随机选择任务执行

- **ContinuationStore**：Future 状态管理
  - [`status` 类型](src/sub_async/eval.ml#L58-L62)：`Pending | Completed | Dependent`
  - [`create`](src/sub_async/eval.ml#L136-L151)：创建 Future 并调度
  - [`await`](src/sub_async/eval.ml#L154-L174)：注册 continuation
  - [`complete`](src/sub_async/eval.ml#L127-L133)：完成时调用 continuations

- **Dependent Future 解析**：
  - [`check_and_resolve_dependent`](src/sub_async/eval.ml#L106-L120)：检查依赖并级联触发
  - [`create_dependent_future`](src/sub_async/eval.ml#L180-L217)：创建依赖型 Future

- **类型系统**：
  - [`Future<T>` 协变 subtyping](src/sub_async/type_check.ml#L99-L101)

---

## 致谢

- **PL Zoo** by Andrej Bauer
- **Supervisor** — 空间/时间解耦设计
