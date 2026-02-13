# Sub_Async Agda Mechanization: Status & Remaining Work

## 当前状态 (2026-02-13 深夜 Session 2 更新 — S-SCHEDULE 已证明!)

### 🎉 WF Preservation 主定理: 9/9 规则全部证明, 零 postulate!

### 已完成 ✅
- [x] 基础框架搭建: SubAsync.agda (AST, Value, State, Configuration)
- [x] WF 不变量定义: WellFormedness.agda (6 条 + fresh-id + 状态操作)
- [x] 9 条规则形式化: Reductions.agda (inductive `_⟶_`)
- [x] WF Preservation 主定理: case 分析结构完整 (WFPreservation.agda)
- [x] 12 个 example reduction step 证明 (Examples.agda)
- [x] 所有文件无 errors / 无 holes 编译通过
- [x] Configuration 用 record `⟪_,_⟫` 避免 parser 歧义
- [x] fresh-id 从 postulate 改为实际函数 (= list length)
- [x] WF 第 5 条件: AllIdsBelow (sequential allocation invariant)
- [x] `queue-add-preserves` — trivial (`there`)
- [x] `lookup-update-same` — `with id ≟ id | yes refl`
- [x] `fresh-id-not-in-domain` — 利用 WF cond5 + `<-irrefl`
- [x] `lookup-prepend-neq` — 不同 key lookup 穿透
- [x] `id-in-domain-prepend` — domain membership 提升
- [x] `all-map` — All predicate lifting
- [x] `M-ASYNC-preserves` — 完整证明 6 条 WF 条件 (~70 行)
- [x] `S-RESOLVE-preserves` — 完整证明 6 条 WF 条件 (~70 行)
- [x] `M-LIFT-OP-preserves` — 完整证明 6 条 WF 条件 (~70 行)
- [x] `S-COMPLETE-preserves` — 完整证明 6 条 WF 条件 (~70 行)
- [x] M-LIFT-OP 规则添加 `id-in-domain` 前提 (Reductions.agda)
- [x] `filter-out` 提升到模块级别 (WellFormedness.agda)
- [x] `filter-out-preserves` / `filter-out-excluded` / `filter-out-inv`
- [x] `nodup-single` / `nodup-pair` — NoDup 小 helper
- [x] WF-preserved 主定理 routing 全部修正
- [x] WF 第 6 条件: `NoDup Q`
- [x] `filter-out-nodup` — filter-out 保持 NoDup
- [x] **S-SCHEDULE 规则修正** — 去掉 merge-futures, 直接用 `get-futures s''`
- [x] **S-SCHEDULE-preserves** — 完整证明 (~250 行), case-split on substep
- [x] **S-SCHEDULE-M-ASYNC-preserves** — 最复杂 case (~100 行), 完整证明 6 条 WF
- [x] **Examples.agda S-SCHEDULE 示例** — 适配新规则 (去掉 ft-merged)
- [x] 辅助引理: `++-identityʳ`, `WF-subst-Q`, `∈-++ˡ`, `∈-++ʳ`, `∈-++-split`, `NoDup-++`, `WF-cond5`
- [x] `pending-update-preserves` — 核心引理: 更新 pending entry 的表达式/环境保持 WF

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
| M-ASYNC | `M-ASYNC-preserves` 完整证明 | ✅ proven |
| M-LIFT-OP-FF/FV/VF | `M-LIFT-OP-preserves` 完整证明 | ✅ proven |
| S-COMPLETE | `S-COMPLETE-preserves` 完整证明 | ✅ proven |
| S-SCHEDULE | `S-SCHEDULE-preserves` case-split on substep (~250 行) | ✅ **proven!** |
| S-RESOLVE | `S-RESOLVE-preserves` 完整证明 | ✅ proven |

**全部 9/9 规则证明完毕! WF Preservation 零 postulate!**

---

## 剩余 Postulates (2 个，与 WF Preservation 无关)

### 独立定理 (不影响 WF Preservation)
1. **`stuck-characterization`** — Stuck ↔ await incomplete + Q=∅ (独立定理)
2. **`NeedsFuture'`** — 辅助谓词 (stuck-characterization 依赖)

### 语言原语 postulates (故意抽象化, 标准做法)
- `Var`, `_≟ᵥ_` — 变量名类型
- `CombineFunction`, `apply-combine` — 组合函数
- `eval-app`, `eval-app-val` — 函数应用
- Examples.agda 中的具体变量名 (`varX`, `testFun` 等)

---

## ICFP 提交前优先级 (deadline: Feb 19 AoE)

### 高优先 (已完成 ✅)
- [x] 填充 `fresh-id-not-in-domain` — 添加 WF 第 5 条件 + `<-irrefl`
- [x] 填充 `lookup-update-same` — 直接 `with id ≟ id | yes refl`
- [x] 填充 `queue-add-preserves` — 就是 `there`
- [x] 填充 `M-ASYNC-preserves` — 完整证明 5 条 WF
- [x] 填充 `S-RESOLVE-preserves` — 完整证明 5 条 WF

### 中优先 (已完成 ✅)
- [x] 填充 `M-LIFT-OP-preserves` — 改签名添加 deps-in-dom + NoDup，完整证明
- [x] 修正 `S-COMPLETE-preserves` — 改签名添加 filter-out，修正主定理 routing

### 低优先 (留作 postulate)
- [ ] `stuck-characterization` — 独立定理，paper 中标明 conjectured

### 已完成 (本 session 新增) ✅
- [x] `S-SCHEDULE-preserves` — case-split on substep, 完整证明 (~250 行)
- [x] S-SCHEDULE 规则修正: 去掉 merge-futures, 直接用 `get-futures s''`
- [x] Examples.agda 适配新规则

---

## 技术笔记

### 语义 vs 实现：非确定性调度
```
语义层面 (Agda):     id ∈Q Q  -- 允许选择 pending set 中任意任务
实现层面 (OCaml):    run_all() = FIFO, run_one_random() = 随机
关键: 非确定性语义 = "所有可能的调度都合法", 证明对任意调度策略成立
```

### Q 是集合不是队列
```
Q 名为 PendingQueue，实际语义上是 set:
- S-SCHEDULE: id ∈ Q (非确定性选取，非 FIFO)
- 所有操作 order-agnostic: prepend/filter-out/++
- WF cond6: NoDup Q 保证无重复
- 保证: M-ASYNC 加入 fresh id (∉ Q), S-COMPLETE 用 filter-out 移除, S-SCHEDULE 的 Q ++ s''.Q 两侧不交
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
