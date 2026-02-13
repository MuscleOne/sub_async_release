# Sub_Async Agda Mechanization

Partial mechanization of λ_fut operational semantics for the ICFP 2026 paper.
~1100 LOC across 5 modules. All 9 reduction rules encoded + 12 example proofs verified.

## 模块结构

```
SubAsync.agda        — AST, Value, Status, State, Configuration    ✅ complete
WellFormedness.agda  — WF(s) 4条不变量 + fresh-id + 状态操作       ✅ complete
Reductions.agda      — 9条规则 (inductive _⟶_)                    ✅ complete
WFPreservation.agda  — WF-preserved 主定理 + stuck-characterization ⚠️ 10 postulates
Examples.agda        — 01_basic + 11_diamond trace (12个证明)       ✅ complete
artifacts/           — 调试用测试脚本（可忽略）
traces/              — OCaml执行trace记录
```

## 当前状态

### 已证明（无 postulate）
- 9条规则作为 inductive relation 通过 type-check ✅
- 12个具体 reduction step 证明 (Examples.agda) ✅
- M-AWAIT / M-AWAIT-IF / M-AWAIT-APP1 / M-AWAIT-APP2 保持 WF（状态不变，trivial）✅
- `queue-add-new` lemma ✅

### Postulates (10个，在 WFPreservation.agda)
| Postulate | 用途 | 难度 |
|-----------|------|------|
| `fresh-id-not-in-domain` | fresh id ∉ dom(Φ) | 中等，最有价值 |
| `lookup-update-same` | prepend 后 lookup 返回新值 | 简单 |
| `queue-add-preserves` | prepend 保持队列成员 | 简单 |
| `M-ASYNC-preserves` | async 后 WF 保持 | 中等，依赖 fresh lemma |
| `M-LIFT-OP-preserves` | lift-op 后 WF 保持 | 中等，依赖 fresh lemma |
| `S-RESOLVE-preserves` | Dependent→Completed 后 WF | 中等 |
| `S-COMPLETE-preserves` | Pending(v)→Completed 后 WF | 中等 |
| `S-SCHEDULE-preserves-generic` | substep 后 WF（最复杂） | 困难 |
| `stuck-characterization` | Stuck ↔ await incomplete + Q=∅ | 困难 |
| `NeedsFuture'` | 辅助谓词 | 简单但需设计 |

### 基础设施 postulates（非证明相关）
- `SubAsync.agda`: `Var`, `_≟ᵥ_`, `CombineFunction`, `apply-combine`
- `Reductions.agda`: `_/_`, `eval-app`, `eval-app-val`, `postulate-var-from-id`
- `Examples.agda`: `varX` ~ `varRight` (测试变量)

## 无类型系统的限制

**可证明**: WF Preservation, Stuck Characterization, 状态单调性
**不可证明**: Progress (untyped 允许 `if 42 then ...`), Type Safety

## 关键设计决策（见 AGDA_vs_SLIDES_DISCREPANCIES.md）

1. `s[id ↦ σ]` 是 **prepend**（shadowing），不是 replace
2. `fresh(Φ) = |Φ|`（确定性，非 slides 中的 non-deterministic choice）
3. `FutureTable = List (Id × Status)`（association list，非 partial function）
4. S-SCHEDULE 使用 `merge-futures` (++) 合并新旧 FutureTable