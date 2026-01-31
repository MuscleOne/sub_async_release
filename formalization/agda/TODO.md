# Sub_Async Agda Mechanization: Roadmap

## 当前状态 (2026-01-31 更新) ✅ ALL 9 RULES PROVEN + WF FRAMEWORK!

### 已完成 ✅
- [x] 基础框架搭建完成 (SubAsync.agda)
- [x] WF不变量定义 (WellFormedness.agda)
- [x] 9条操作语义规则框架 (Reductions.agda)
- [x] 证明结构框架 (WFPreservation.agda)
- [x] 所有文件可以load（无holes/无errors）
- [x] **Parser问题解决** - Configuration改为record `⟪_,_⟫` 避免歧义
- [x] **fresh-id实现** - 从postulate改为实际函数定义
- [x] **Examples.agda完整trace** - 01_basic.sub 和 11_diamond_dependency.sub
- [x] **所有9条规则验证完成！** 🎉
- [x] **WF Preservation框架** - 主定理 + case分析结构 ✅ NEW!

### 已验证的证明 (12个) ✅ COMPLETE COVERAGE!
```agda
-- M-ASYNC (2个 + inner-step)
example1-step0→1 = M-ASYNC           -- async (2+3) → Future #0
example2-step0→1 = M-ASYNC           -- async 1000 → Future #0

-- M-LIFT-OP-* (3个) - 完整覆盖！
lift-ff-proof = M-LIFT-OP-FF         -- Future#0 + Future#1 → Dependent
lift-fv-proof = M-LIFT-OP-FV         -- Future#0 + Value → Dependent  
lift-vf-proof = M-LIFT-OP-VF         -- Value + Future#0 → Dependent

-- S-COMPLETE (1个)
complete-proof = S-COMPLETE ...      -- Pending(value) → Completed

-- M-AWAIT (1个)
await-proof = M-AWAIT ...            -- 从completed Future提取值

-- M-AWAIT-IF/APP (3个) - 完整覆盖！
await-if-proof = M-AWAIT-IF ...      -- if条件中的await
await-app1-proof = M-AWAIT-APP1 ...  -- app函数位置await
await-app2-proof = M-AWAIT-APP2 ...  -- app参数位置await

-- S-RESOLVE (1个)
resolve-proof = S-RESOLVE ...        -- Dependent → Completed (当所有deps完成)

-- S-SCHEDULE (1个) - 最复杂的规则！
schedule-proof = S-SCHEDULE ...      -- 执行pending Future的一步 (嵌套证明!)
```

### WF Preservation (WFPreservation.agda) ✅ NEW!
```agda
-- 主定理：WF-preserved
WF-preserved : ∀ {c c'} → WF (cfg-state c) → c ⟶ c' → WF (cfg-state c')

-- 已完成的case (直接证明):
M-AWAIT-preserves       -- 状态不变，trivial
M-AWAIT-IF-preserves    -- 状态不变，trivial
M-AWAIT-APP1-preserves  -- 状态不变，trivial
M-AWAIT-APP2-preserves  -- 状态不变，trivial

-- 结构完整的case (用postulate lemmas):
M-ASYNC-preserves       -- fresh-id保证新id
M-LIFT-OP-preserves     -- deps存在 + 无自引用
S-RESOLVE-preserves     -- completed无deps
S-COMPLETE-preserves    -- 从Q移除 + 标记completed
S-SCHEDULE-preserves    -- 最复杂，使用generic postulate

-- Stuck Characterization定理框架:
stuck-characterization  -- 系统卡住 ⟺ 等待incomplete Future + Q=∅
```

### 里程碑总结 🎉
1. ✅ 所有9条规则都有验证通过的证明
2. ✅ WF Preservation主定理完整case分析
3. ✅ Stuck Characterization定理声明
4. ✅ 所有文件无errors/无holes编译通过

### 语义 vs 实现：非确定性调度
```
语义层面 (Agda):     id ∈Q Q  -- 允许选择队列中任意任务
实现层面 (OCaml):    run_all() = FIFO, run_one_random() = 随机

关键洞察: 这不是冲突！
- 非确定性语义 = "所有可能的调度都是合法的"
- FIFO/随机 = "其中一种特定的调度"
- 证明对所有调度策略都成立！
```

### 核心文件结构
```
formalization/agda/
├── SubAsync.agda        # 语法、值、状态定义
├── WellFormedness.agda  # WF不变量 + fresh-id + 状态操作
├── Reductions.agda      # 9条操作语义规则 + value-to-expr
├── WFPreservation.agda  # WF Preservation + Stuck定理 ✅ UPDATED
├── Examples.agda        # 完整trace + 12个已验证证明
├── artifacts/           # 调试用的测试脚本（可忽略）
└── traces/              # OCaml执行trace记录
```

## 下一步工作 (Optional)

### 填充Postulate (需要更多辅助引理)
1. `fresh-id-not-in-domain` - 证明fresh-id不在当前域中
2. `lookup-update-same` - 更新后lookup返回新值
3. 各个 *-preserves lemma 的完整证明

### 扩展
1. 添加更多execution trace examples
2. 完善Stuck定理的实际证明
3. 考虑添加Progress定理

## Phase 1: 填补Holes并验证例子 ✅ 已完成!
- `example1-step0` 到 `example1-final` (01_basic.sub完整trace)
- `example2-step0` 到 `example2-final` (11_diamond_dependency.sub完整trace)

### 1.3 证明步骤有效 ✅ 部分完成
```agda
example1-step0→1 : example1-step0 ⟶ example1-step1
example1-step0→1 = M-ASYNC  -- ✅ Agda验证通过！

example2-step0→1 : example2-step0 ⟶ example2-step1
example2-step0→1 = M-ASYNC  -- ✅ Agda验证通过！
```

### 1.4 待做：更多步骤的证明 🎯
已证明的规则：
- [x] M-ASYNC (2个例子)
- [x] M-LIFT-OP-FF (Future + Future → Dependent) ✅
- [x] M-LIFT-OP-FV (Future + Value → Dependent) ✅ NEW!
- [x] M-LIFT-OP-VF (Value + Future → Dependent) ✅ NEW!
- [x] S-COMPLETE (Pending → Completed)
- [x] M-AWAIT (从completed提取值)
- [x] S-RESOLVE (Dependent → Completed)

剩余待证明：
- [ ] S-SCHEDULE: 执行pending任务的一步 (最复杂)
- [ ] M-AWAIT-IF: if条件中的await
- [ ] M-AWAIT-APP1: app函数位置的await
- [ ] M-AWAIT-APP2: app参数位置的await

**重要发现**: `update-future` 是**添加**到列表前面，不是**替换**！
这意味着FutureTable可能有同一个id的多个条目，lookup会返回第一个（最新的）。

## Phase 2: 证明WF Preservation 🔍 (核心定理)

### 2.1 分case证明
在 `WFPreservation.agda` 的 `WF-preserved` 函数中：

```agda
WF-preserved wf-s M-ASYNC = {!!}         -- 证明M-ASYNC保持WF
WF-preserved wf-s M-LIFT-OP-FF = {!!}    -- 证明M-LIFT-OP保持WF
-- ... 对每个规则分别证明
```

每个case需要证明：
- 如果 WF(s) 成立
- 并且 ⟨e, s⟩ → ⟨e', s'⟩ 通过某个规则
- 那么 WF(s') 也成立

### 2.2 辅助lemma
你可能需要证明一些辅助引理：
```agda
fresh-id-not-in-domain : ∀ Φ → let id = fresh-id Φ in ¬ (id-in-domain id Φ)
update-preserves-wf : ∀ s id σ → WF s → WF (update-future s id σ)
```

## Phase 3: 证明Stuck Characterization 🎭 (你们的独特贡献)

在 `WFPreservation.agda` 中填补 `stuck-characterization` 的证明：

这个定理说：
**系统卡住 ⟺ (主表达式await未完成Future) ∧ (队列为空)**

这是Sub_Async的关键性质，证明了：
1. 系统不会"无故卡死"
2. 如果卡住，一定是在等待某个具体的Future
3. 并且队列里没有任务可以推进

## Phase 4: 与OCaml实现对比 🔄 (可选但很有价值)

### 4.1 Bisimulation证明
证明Agda语义和OCaml实现是等价的：
```agda
agda-matches-ocaml : ∀ example → 
  (ocaml-trace example) ≡ (agda-trace example)
```

### 4.2 找到Bug
通过对比可能发现：
- OCaml实现的bug
- 形式化语义的遗漏
- Edge case处理不一致

## Alternative路径：快速验证工具

如果Agda证明太难，可以：

### Option A: PLT Redex (强烈推荐！)
```racket
;; 可执行语义 + 自动测试
(define-language sub-async ...)
(define-reduction step ...)
(redex-check step property)  ; 自动找反例！
```

### Option B: QuickCheck风格测试
```agda
-- 生成随机trace并检查性质
postulate quickcheck : (c : Configuration) → Bool
```

## 优先级建议 (更新后)

### ✅ 已完成：
1. ✅ 运行例子并收集trace
2. ✅ 在Examples.agda中构造完整trace (01_basic, 11_diamond)
3. ✅ **6个规则的证明通过**: M-ASYNC, M-LIFT-OP-FF, S-COMPLETE, M-AWAIT, S-RESOLVE
4. ✅ Parser问题解决
5. ✅ fresh-id实现

### 🎯 下一步 (优先级顺序)：
1. **证明 M-LIFT-OP-FV / VF** - 完成所有LIFT变体
2. **开始 WF Preservation** - 用已有的证明作为case基础
3. **证明 S-SCHEDULE** - 这是最复杂的规则

### 📅 短期目标（2周内）：
1. 完成Examples.agda中更多步骤的证明
2. 证明至少2个规则的WF preservation
3. 理解S-RESOLVE的依赖检查机制

### 🎯 长期目标（1个月）：
1. 完成WF Preservation完整证明
2. 证明Stuck Characterization
3. （可选）写paper展示formalization

## 技术笔记

### Parser问题解决方案
- Configuration从 `Expr × State` 改为 record with `⟪_,_⟫`
- FutureTable条目用命名定义避免inline pair解析问题
- 必须在SubAsync导入后再导入 `Data.Product using (_,_)`

### fresh-id实现
```agda
fresh-id : FutureTable → Id  
fresh-id [] = zero
fresh-id (_ ∷ rest) = suc (fresh-id rest)
```
返回FutureTable长度，保证ID不重复

## 学习资源

- **Agda入门**: PLFA (Programming Language Foundations in Agda)
- **证明技巧**: 看aeff-formalization的Progress.agda  
- **调试技巧**: 在Emacs中用 C-c C-l (load), C-c C-c (case split), C-c C-r (refine)

## 求助信号

如果遇到以下情况，可以寻求帮助：
- Agda报错看不懂
- 某个证明卡住超过2小时
- 不确定如何构造某个configuration
- 想用Redex但不知道从哪开始

你现在有了完整的框架，最关键的是**用你的例子来验证规则**！这样即使证明没做完，你也能确信规则是对的。
