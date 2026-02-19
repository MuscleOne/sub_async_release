# Agda Formalization Structure Analysis / Agda 形式化结构分析

> 生成日期: 2026-02-19. 适用于清理 MAsyncProof.agda 之后的代码库（~2789 LOC, 7 modules）.

---

## 一、文件行数与职责分布 / File Sizes & Responsibilities

| File | Lines | Role |
|------|-------|------|
| `SubAsync.agda` | 133 | AST、Value、Status（Pending/Completed/Dependent）、State `⟨ρ,Φ,Q⟩`、Configuration |
| `WellFormedness.agda` | 102 | WF 谓词（6 个不变量）、`fresh-id`、state 操作（update/add/remove） |
| `Reductions.agda` | 181 | 9 条归约规则（`_⟶_` 归纳类型）+ combine 辅助函数 |
| `Types.agda` | 315 | Ty、子类型 `<:`、类型判断 `Σ；Γ ⊢ e ∶ τ`、WT（Well-Typed State）定义 |
| `WFPreservation.agda` | **909** | **WF 保持定理：9/9 规则全部证明，零 postulate** |
| `TypePreservation.agda` | 600 | 类型保持：8/9 规则 case 已证；S-SCHEDULE + 主定理仍 postulate |
| `Examples.agda` | 549 | 两个具体执行轨迹（basic + diamond），12 个 step 证明 |
| **Total** | **~2789** | |

### 已归档文件 / Archived Files

| File | Location | Note |
|------|----------|------|
| `MAsyncProof.agda` (165 lines) | `artifacts/` | M-ASYNC 证明的独立早期草稿，内容已被 `WFPreservation.agda` 完全覆盖 |

---

## 二、Import 依赖结构 / Module Dependency Graph

```
SubAsync              ← 无项目内依赖（leaf module）
  ↑
WellFormedness        ← imports SubAsync
  ↑
Reductions            ← imports SubAsync, WellFormedness
  ↑
Types                 ← imports SubAsync (独立于 Reductions)
  ↑
WFPreservation        ← imports SubAsync, WellFormedness, Reductions
TypePreservation      ← imports SubAsync, WellFormedness, Reductions, Types
Examples              ← imports SubAsync, WellFormedness, Reductions
```

**关键特点**: `Types.agda` 和 `Reductions.agda` 互不依赖——类型系统和操作语义是分离定义的。
`TypePreservation` 是唯一同时依赖两者的文件。

外部依赖全部来自 Agda 标准库：`Data.List`, `Data.Nat`, `Data.Maybe`, `Data.Product`,
`Relation.Binary.PropositionalEquality` 等。

---

## 三、WF 不变量定义 / Well-Formedness Invariant (6 Conditions)

定义在 `WellFormedness.agda` 的 `data WF (s : State)` 中：

| # | Condition | 含义 |
|---|-----------|------|
| cond1 | `id ∈ Q ↔ Φ(id) = pending(e,ρ)` | Q 精确跟踪所有 pending future |
| cond2 | `∀d ∈ deps(Φ(id)). d ∈ dom(Φ)` | No dangling dependencies（无悬空依赖） |
| cond3 | `dependent(deps,f) ⇒ id∉deps ∧ NoDup(deps)` | No self-cycles, no duplicate deps |
| cond4 | `ρ(x) = futureV(id) ⇒ id ∈ dom(Φ)` | No dangling Future refs in env |
| cond5 | `Φ(id)↓ ⇒ id < fresh-id(Φ)` | Sequential allocation invariant |
| cond6 | `NoDup(Q)` | Q is semantically a set |

---

## 四、9 条归约规则 × 证明状态 / 9 Reduction Rules × Proof Status

### WF Preservation（全部完成，零 postulate ✅）

| Rule | State Change | WF Proof Technique | Lines |
|------|--------------|--------------------|-------|
| M-AWAIT ×4 | 状态不变 | trivial: `wf-s → wf-s` | ~12 |
| M-ASYNC | Φ += pending; Q += id | 6 条件逐一重建，cond1 双向 + cond6 freshness | ~80 |
| M-LIFT-OP ×3 (FF/FV/VF) | Φ += dependent | 共享引理 `M-LIFT-OP-preserves`（deps-in-dom + NoDup 作前提） | ~100 |
| S-COMPLETE | Φ: pending→completed; Q -= id | `filter-out` 系列引理（4 个） | ~100 |
| S-RESOLVE | Φ: dependent→completed | Non-empty deps → `just-inj` + pending≠dependent | ~50 |
| S-SCHEDULE | 递归：子步骤归约 + merge Φ,Q | **最复杂**：对 9 种子步骤 case-split（其中 2 种 impossible） | ~200 |

### Type Preservation（8/9 已证 + 3 postulates）

| Rule | Status | Technique |
|------|--------|-----------|
| M-AWAIT | ✅ proven | `future-lit-inversion` + WT lookup + `value-to-expr-typed` |
| M-AWAIT-IF | ✅ proven | `if-inversion` + `eval-if-typed` case analysis |
| M-ASYNC | ✅ proven | `⊇-fresh` + `T-FutureLit` + `lookup-store-same` |
| M-LIFT-OP ×3 | ✅ proven | Same technique as M-ASYNC |
| S-COMPLETE | ✅ proven | `expr-to-value-typed` + WT reconstruction |
| S-RESOLVE | ✅ proven | `collect-values-length` + `ET-Dependent` extraction |
| S-SCHEDULE | ❌ postulate | Inductive substep; structurally similar to WF case |
| Main theorem | ❌ postulate | Wraps all cases |
| `funV-typing` | ❌ postulate | Closure typing bridge (semantically justified) |

---

## 五、引理层级 / Lemma Hierarchy

### WFPreservation 的 5 层引理结构

**Layer 1 — 工具引理（~50 lines）**
- `lookup-update-same` / `lookup-prepend-neq` / `id-in-domain-prepend`：Future table prepend 操作
- `all-map`：`All` 谓词映射
- `fresh-id-not-in-domain`：freshness 核心引理（cond5 + `<-irrefl`）

**Layer 2 — filter-out 系列（~50 lines, for S-COMPLETE）**
- `filter-out-preserves`：非目标元素在 filter 后幸存
- `filter-out-excluded`：目标元素被排除
- `filter-out-inv`：filter 后成员属于原始列表
- `filter-out-nodup`：NoDup 经 filter 保持

**Layer 3 — 列表操作引理（~40 lines, for S-SCHEDULE）**
- `∈-++ˡ` / `∈-++ʳ` / `∈-++-split`：append 后的成员关系
- `NoDup-++`：两个 NoDup 列表的拼接

**Layer 4 — per-rule preserves 函数（~600 lines）**
- 每个非平凡规则生成一个 preserves 函数
- 内部对 6 个 WF 条件逐一证明
- 每个条件由 `Dec (id ≡ fresh-id)` 驱动 yes/no 分支
- 5 非平凡规则 × 6 条件 × 2 分支 ≈ 60 个子证明块

**Layer 5 — 主定理 `WF-preserved`（~10 lines）**
- 对 `c ⟶ c'` 做 case-split，调用各 preserves 函数

### TypePreservation 的引理结构

**Value-Expr Bridge**
- `value-to-expr-typed`：Value typing → Expr typing（4 cases, all proven）
- `expr-to-value-typed`：Expr typing → Value typing（3/4 proven, funV uses postulate）

**Inversion Lemmas**
- `future-lit-inversion` / `num-inversion` / `bool-inversion` / `fun-inversion` / `if-inversion`

**Combine Function Typing**（all proven, ~120 lines of case exhaustion）
- `apply-op-typed`：穷举 6×4×4 combinations
- `combine-binary-typed` / `combine-unary-left-typed` / `combine-unary-right-typed`

**Store Extension**
- `⊇-fresh`：WF+WT → `fresh-id ∉ dom(Σ)` → prepend preserves lookups

---

## 六、行数多的根本原因 / Root Causes for High LOC

1. **逐条件、逐分支的 boilerplate**：每个 preserves 引理必须对 WF/WT 的全部条件逐一重建。
   每个条件 `Dec (id ≡ fresh-id)` → yes/no → 各 5–15 行。

2. **单调 prepend 模型**：`Φ` 用 `(id,σ) ∷ Φ` 实现"更新"（首匹配语义），
   每次状态变化都需要 `lookup-prepend-neq` 桥接，产生大量机械化样板。

3. **S-SCHEDULE 的双重递归**：S-SCHEDULE 规则内嵌子步骤归约
   `⟪ e', ⟨ ρ', Φ, [] ⟩ ⟫ ⟶ ⟪ e'', s'' ⟫`，
   证明必须对所有 9 种可能子步骤再做 case-split（其中 S-SCHEDULE/S-COMPLETE impossible because Q=[]），约 200 行。

4. **穷举式类型安全**：`apply-op-typed` 对 6 ops × 4 value forms × 4 value forms 逐一穷举
   非法组合返回 `nothing` 的 absurdity。

5. **Examples.agda 纯体积**（549 lines）：手工构造完整 FutureTable、Configuration、
   `refl` 证明，有验证价值但可机械压缩。

---

## 七、Trust Summary / 信任边界总结

| Category | Postulates | Note |
|----------|------------|------|
| WF Preservation | **0** | 完全机械化 ✅ |
| Type Preservation | 3 | `funV-typing` (semantic), `S-SCHEDULE-type-preserves`, `type-preserved` |
| Infrastructure | ~5 | `Var`, `_≟ᵥ_`, `eval-app`, `eval-app-val`, `_/_` (division) |
| Examples | 5 | Concrete variable names (`varX`, `varY`, etc.) |
