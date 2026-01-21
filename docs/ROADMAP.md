# Sub_Async: 研究路线图

## 当前状态

### ✅ Phase 1: OCaml 实现（已完成）

**交付物：**
- `src/sub_async/` — Complete implementation
  - `syntax.ml` — AST with `Async`, `Future`, `TFuture`
  - `eval.ml` — CPS evaluator with operator polymorphism
  - `future.ml` — State machine (Pending/Completed/Dependent)
  - `scheduler.ml` — Non-deterministic task queue
  - `type_check.ml` — Type system with `future<T>` support

**关键设计决策：**
- Operator polymorphism: `+` 自动检测 Future 类型
- Implicit coordination: 无需显式 `await`
- Static dependency graphs: 在运算符应用时构建

**文档：**
- `docs/DESIGN_DECISIONS.md` — Trade-offs
- `docs/SLIDES_SHORT.md` — Presentation slides

---

## 🚧 Phase 2: Operational Semantics 设计（进行中）

### 目标
为 Sub_Async 设计 small-step operational semantics 和 type system，适合在 Agda 中进行形式化验证。

### 学习任务

#### Task 2.1: 分析 Aeff Implementation
**来源：** `external_resources/aeff-implementation/`

**重点关注：**
- [ ] `src/syntax.ml` — How do they define operations and handlers?
- [ ] `src/eval.ml` — How do they implement effect interpretation?
- [ ] `src/infer.ml` — How do they type operations and handlers?

**需要回答的问题：**
1. Aeff 如何将 "async" 表示为一个 effect？
2. 它们的 handler 机制与我们的 scheduler 有何不同？
3. 它们如何处理 effect polymorphism in types？

#### Task 2.2: 分析 Aeff Formalization
**来源：** `external_resources/aeff-formalization/`

**重点关注：**
- [ ] `Syntax.agda` — Inductive definitions for syntax
- [ ] `Semantics.agda` — Small-step rules
- [ ] `TypeSystem.agda` — Typing judgments
- [ ] `Soundness.agda` — Progress + Preservation proofs

**需要回答的问题：**
1. 它们如何定义 configuration (state)？
2. 它们如何在 semantics 中处理 non-determinism？
3. 它们为 type safety 维护了哪些 invariants？

#### Task 2.3: 阅读论文
**来源：** `external_resources/async-effects-paper/`

**关键章节：**
- [ ] `basic-calculus-computations.tex` — Core calculus rules
- [ ] `basic-calculus-processes.tex` — Process semantics
- [ ] `aeff.tex` — Full language specification

---

### 对比分析

#### Aeff vs Sub_Async: 概念映射

| Aeff 概念 | Sub_Async 对应概念 | 备注 |
|-----------|-------------------|------|
| Operation call | `async e` | 都将计算 "抛" 到别处 |
| Handler | Scheduler + Future resolution | Aeff 显式，我们隐式 |
| Effect row | `future<T>` type | Aeff 更通用（多种 effects） |
| Continuation | `continuation list` in status | 都在内部使用 CPS |
| Runner | `Scheduler.run_all` | 都执行直到完成 |

#### 关键差异

**1. 协调模型**
- **Aeff:** 显式 handlers — 程序员写 `handle ... with ...`
- **Sub_Async:** 隐式协调 — operators 自动检测 Futures

**2. Effect 作用域**
- **Aeff:** 多种 effects，effect polymorphism
- **Sub_Async:** 单一 effect (async)，更简单的 type system

**3. 依赖追踪**
- **Aeff:** 动态（handler 可以检查 continuation）
- **Sub_Async:** 静态（dependency graph 在 operator 时构建）

**4. Semantics 风格**
- **Aeff:** Big-step with handlers, small-step for processes
- **Sub_Async:** 待定 — 可能全部用 small-step

---

### Core Calculus 设计草案

参考 Aeff 论文和形式化的做法，我们的 Core Sub_Async 演算应该聚焦 Future 机制：

**值 (Values):**
```
V ::= n                    (整数字面量)
    | x                    (变量)
    | fut_id               (Future 引用)
```

**表达式 (Expressions):**
```
e ::= V                    (值)
    | e₁ ⊕ e₂             (二元运算)
    | async e              (异步块)
    | let x = e₁ in e₂    (let 绑定)
```

**运算符:**
```
⊕ ::= + | * | - | <       (统一的二元运算，区分具体操作)
```

**配置 (Configuration):**
```
Σ = ⟨e, ρ, Φ, Q⟩
  e — 当前表达式
  ρ — 环境 (x → V)
  Φ — Future table (fut_id → FutureStatus)
  Q — Task queue (待执行的 fut_id 集合)

FutureStatus ::= Pending(e, ρ)
               | Completed(V)
               | Dependent([fut_id], ⊕)
```

---

### 待决定的设计问题

#### D1: Configuration 结构
```
⟨e, ρ, Σ, Q⟩
```
- `e` — Current expression
- `ρ` — Environment
- `Σ` — Future table (id → status)
- `Q` — Task queue

**待解决问题：** 是否应该将 "main thread" 与 "background tasks" 分离？

#### D2: Small-Step 规则

**Async 创建：**
```
⟨async e, ρ, Σ, Q⟩ → ⟨n, ρ, Σ[n ↦ Pending(e,ρ)], Q ∪ {n}⟩
```

**Operator 提升：**
```
⟨n₁ + n₂, ρ, Σ, Q⟩ → ⟨m, ρ, Σ[m ↦ Dependent([n₁,n₂], (+))], Q⟩
  where Σ(n₁) ≠ Completed ∨ Σ(n₂) ≠ Completed
```

**Scheduler 步骤（非确定性）：**
```
⟨v, ρ, Σ, Q⟩ →_sched ⟨v, ρ, Σ', Q'⟩
  where some task in Q takes a step
```

**待解决问题：** 如何形式化 non-determinism？用 LTS labels？

#### D3: Type System

**Async 的类型规则：**
```
Γ ⊢ e : T
─────────────────
Γ ⊢ async e : future<T>
```

**Operator 提升的类型规则：**
```
Γ ⊢ e₁ : future<int>    Γ ⊢ e₂ : future<int>
──────────────────────────────────────────────
Γ ⊢ e₁ + e₂ : future<int>
```

**待解决问题：** 要不要 Subtyping？`int <: future<int>`？

---

## Phase 3: Agda 形式化（计划中）

### 验证范围决策

参考 Aeff 的做法，采用**渐进式验证策略**：

#### Phase 3a: Core Calculus 验证（必做，Week 5-8）

**语法（极简版）：**
```
值 V ::= n | x | fut_id
表达式 e ::= V | e₁ ⊕ e₂ | async e | let x = e₁ in e₂
运算符 ⊕ ::= + | * | - | <  （抽象的二元运算）
```

**简化掉的特性：**
- ❌ 布尔类型和 `if` 表达式（已知有 short-circuit 问题）
- ❌ 函数 `Fun`/`Apply`（用 `let` 绑定足够展示环境捕获）
- ❌ 比较运算返回 `Future<bool>`（类型系统简化）

**保留的核心机制：**
- ✅ `async e` → 创建 Future
- ✅ `fut_id ⊕ fut_id` → Operator polymorphism（自动提升）
- ✅ Dependency graph 构建
- ✅ Non-deterministic scheduling

**验证目标：**
1. **Progress:** Well-typed 的程序不会 stuck
2. **Preservation:** Types 在 reduction 中保持不变
3. **Future Resolution:** 所有 Dependent Futures 最终都会 resolve（在 fair scheduling 下）

---

#### Phase 3b: 扩展验证（如果时间允许）

按优先级逐步添加：
1. **条件分支：** 添加 `if` 表达式和布尔类型
2. **函数：** 添加 `Fun`/`Apply`，验证闭包和环境语义
3. **完整运算符：** 区分不同算术运算的具体语义

---

### 目录结构
```
formalization/
├── agda/
│   ├── Syntax.agda          -- Core calculus 语法
│   ├── Semantics.agda       -- Small-step rules
│   ├── TypeSystem.agda      -- Typing judgments
│   ├── Progress.agda        -- Progress 定理
│   ├── Preservation.agda    -- Preservation 定理
│   └── FutureResolution.agda -- Future 最终 resolve 的证明
└── README.md
```

---

## 时间线（暂定）

| 周次 | 任务 |
|------|------|
| Week 1-2 | 分析 Aeff implementation + 论文 |
| Week 3 | 在纸上草拟 Core Calculus 的 small-step rules |
| Week 4 | 与导师讨论（确认验证范围和策略）|
| Week 5-6 | Agda 形式化：Syntax + Semantics + TypeSystem |
| Week 7-8 | 证明 Progress + Preservation |
| Week 9+ | （可选）扩展验证：添加 if/Fun 等特性 |

---

## 给导师的问题

1. **Non-determinism:** Aeff 使用 labeled transitions，我们也应该这样吗？

2. **范围：** 应该形式化整个语言还是 core calculus？
   - **Aeff 的做法：** 形式化核心演算（去掉 Tuple、Variant、模式匹配等）
   - **建议：** 先形式化 Core Sub_Async（保留 `async`、`Future`、operator polymorphism 核心机制）
   - **原因：** 专注于 Future 机制的 soundness，避免陷入语言特性细节

3. **Short-circuit:** 在形式化之前要不要先解决 boolean operator 的问题？
   - **建议：** Core calculus 中可以直接去掉布尔运算，用抽象的二元运算 `⊕` 代替

4. **参考文献：** 还有其他关于 Future/Promise semantics 的论文要读吗？

---

## 参考文献

### 主要参考
- Ahman, D. & Pretnar, M. — Aeff paper (in `external_resources/async-effects-paper/`)
- Ahman, D. — Aeff Agda formalization (in `external_resources/aeff/formalization/`)

### 背景知识
- Pierce, B. — Types and Programming Languages (TAPL)
- Harper, R. — Practical Foundations for Programming Languages (PFPL)
- Software Foundations — PLF volume (Coq, but applicable)
- PLFA — Programming Language Foundations in Agda

### 相关工作
- Scala Futures formal semantics
- Concurrent ML semantics
- Algebraic effects literature (Plotkin & Pretnar)
