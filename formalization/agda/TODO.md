# Sub_Async Agda Mechanization: Status & Remaining Work

## 当前状态 (2026-02-13 更新)

### 已完成 ✅
- [x] 基础框架搭建: SubAsync.agda (AST, Value, State, Configuration)
- [x] WF 不变量定义: WellFormedness.agda (4 条 + fresh-id + 状态操作)
- [x] 9 条规则形式化: Reductions.agda (inductive `_⟶_`)
- [x] WF Preservation 主定理: case 分析结构完整 (WFPreservation.agda)
- [x] 12 个 example reduction step 证明 (Examples.agda)
- [x] 所有文件无 errors / 无 holes 编译通过
- [x] Configuration 用 record `⟪_,_⟫` 避免 parser 歧义
- [x] fresh-id 从 postulate 改为实际函数 (= list length)

### 已验证的 12 个证明 (Examples.agda)
```
M-ASYNC ×2         — async (2+3), async 1000
M-LIFT-OP-FF ×1    — Future#0 + Future#1 → Dependent
M-LIFT-OP-FV ×1    — Future#0 + Value → Dependent
M-LIFT-OP-VF ×1    — Value + Future#0 → Dependent
S-COMPLETE ×1      — Pending(value) → Completed
M-AWAIT ×1         — 从 completed Future 提取值
M-AWAIT-IF ×1      — if 条件中的 await
M-AWAIT-APP1 ×1    — app 函数位置 await
M-AWAIT-APP2 ×1    — app 参数位置 await
S-RESOLVE ×1       — Dependent → Completed (所有 deps 完成)
S-SCHEDULE ×1      — 执行 pending Future 一步 (嵌套证明)
```

### WF-preserved 主定理分析
```agda
WF-preserved : ∀ {c c'} → WF (cfg-state c) → c ⟶ c' → WF (cfg-state c')
```

| Rule | 证明方式 | 状态 |
|------|---------|------|
| M-AWAIT | 直接 (`wf-s = wf-s`, 状态不变) | ✅ proven |
| M-AWAIT-IF | 直接 (同上) | ✅ proven |
| M-AWAIT-APP1 | 直接 (同上) | ✅ proven |
| M-AWAIT-APP2 | 直接 (同上) | ✅ proven |
| M-ASYNC | `M-ASYNC-preserves` postulate | ⚠️ postulated |
| M-LIFT-OP-FF/FV/VF | `M-LIFT-OP-preserves` postulate | ⚠️ postulated |
| S-COMPLETE | 路由到 `S-SCHEDULE-preserves-generic` | ⚠️ postulated |
| S-SCHEDULE | `S-SCHEDULE-preserves-generic` postulate | ⚠️ postulated |
| S-RESOLVE | `S-RESOLVE-preserves` postulate | ⚠️ postulated |

**注意**: S-COMPLETE 当前路由到 `S-SCHEDULE-preserves-generic` 而非 `S-COMPLETE-preserves`。

---

## 剩余 Postulates (10 个)

### 辅助 lemma（优先填充）
1. **`fresh-id-not-in-domain`** — `¬ (id-in-domain (fresh-id Φ) Φ)`. 最关键，解锁 M-ASYNC 和 M-LIFT-OP.
2. **`lookup-update-same`** — `lookup-future ((id , σ) ∷ Φ) id ≡ just σ`. 直接的 list lemma.
3. **`queue-add-preserves`** — `id' ∈ Q → id' ∈ (id ∷ Q)`. trivial (= `there`).

### Case-level lemma（依赖辅助 lemma）
4. **`M-ASYNC-preserves`** — async 创建 Pending + 加入 Q 后 WF 保持
5. **`M-LIFT-OP-preserves`** — 创建 Dependent 后 WF 保持
6. **`S-RESOLVE-preserves`** — Dependent→Completed 后 WF 保持
7. **`S-COMPLETE-preserves`** — Pending(v)→Completed + 从 Q 移除后 WF 保持

### 困难 postulates
8. **`S-SCHEDULE-preserves-generic`** — substep 后 WF 保持（最复杂，涉及 merge）
9. **`stuck-characterization`** — Stuck ↔ await incomplete + Q=∅
10. **`NeedsFuture'`** — 辅助谓词（需要设计 enumeration of all expression contexts）

---

## ICFP 提交前优先级 (deadline: Feb 19 AoE)

### 高优先 (Feb 15 前)
- [ ] 填充 `fresh-id-not-in-domain` — 对 list length 做 induction
- [ ] 填充 `lookup-update-same` — 直接 `with id ≟ id | yes refl`
- [ ] 填充 `queue-add-preserves` — 就是 `there`

### 中优先 (Feb 17 前)
- [ ] 填充 `M-ASYNC-preserves` — 用 fresh lemma + WF invariant 分别证 4 条
- [ ] 填充 `S-COMPLETE-preserves` — 需要 remove-from-queue 的 lemma

### 低优先 (留作 postulate)
- [ ] `S-SCHEDULE-preserves-generic` — 太复杂，paper 中标明 postulated
- [ ] `stuck-characterization` — 太复杂，paper 中标明 conjectured

---

## 技术笔记

### 语义 vs 实现：非确定性调度
```
语义层面 (Agda):     id ∈Q Q  -- 允许选择队列中任意任务
实现层面 (OCaml):    run_all() = FIFO, run_one_random() = 随机
关键: 非确定性语义 = "所有可能的调度都合法", 证明对任意调度策略成立
```

### state update 是 prepend 不是 replace
```agda
update-future ⟨ ρ , Φ , Q ⟩ id σ = ⟨ ρ , (id , σ) ∷ Φ , Q ⟩
```
lookup 返回第一个匹配（最新的），older entries 被 shadow。
详见 AGDA_vs_SLIDES_DISCREPANCIES.md。

### fresh-id = list length
```agda
fresh-id [] = zero
fresh-id (_ ∷ rest) = suc (fresh-id rest)
```
因为 prepend 只增不减，length 严格递增，保证 freshness。
但证明 `fresh-id-not-in-domain` 需要 induction on Φ + 利用 id 分配的单调性。
