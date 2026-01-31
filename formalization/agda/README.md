# Sub_Async Agda Mechanization

## 为什么不需要类型系统也能mechanize？

你同事说得对！虽然没有类型系统，但Sub_Async的操作语义仍然可以mechanize很多**有价值**的性质：

### 🎯 可以证明的核心性质

1. **WF Preservation** (最重要)
   ```agda
   WF-preserved : ∀ {c c'} → WF (proj₂ c) → c ⟶ c' → WF (proj₂ c')
   ```
   - 这保证系统始终"健康"
   - id freshness、无悬空引用、依赖图有界等

2. **Stuck Characterization** (很有用)  
   ```agda  
   stuck-characterization : 系统卡住 ↔ (主表达式await未完成Future ∧ Q = ∅)
   ```
   - 精确刻画系统何时"真正卡死"
   - 证明scheduler的"必要性"

3. **Deterministic State Updates** (基础性质)
   - Fresh id生成的确定性
   - Future状态转换的单调性  
   - Dependency图的无环性

### 🚫 不能证明的性质（需要类型）

- **Progress**: `¬ Stuck c → ∃ c' (c ⟶ c')` 
  - 因为untyped表达式可能type error
  - 例如: `if 42 then e₁ else e₂` 会卡住
- **Type Safety**: `⊢ e : τ → ∃ v (e →* v)`
  - 显然没有类型系统就没有type safety

## 📁 模块结构

```
SubAsync.agda           -- 语法、值、状态定义
WellFormedness.agda     -- WF(s)不变量定义  
Reductions.agda         -- 9条操作语义规则
WFPreservation.agda     -- 主要证明：WF保持性
StuckCharacterization.agda  -- 卡住条件刻画
Examples.agda           -- 具体执行trace
```

## 🔄 与Aeff的对比

| 方面 | Aeff | Sub_Async |
|------|------|-----------|
| **类型** | 有完整类型系统 | Untyped |  
| **可证明** | Progress + Preservation | WF Preservation + Stuck Characterization |
| **复杂度** | ~15个规则 | 9个规则 |
| **并行** | 显式 `P ∥ Q` | 隐式队列调度 |

## 🛠 推荐的mechanization路径

### Phase 1: 基础框架 ✅
- [x] 语法和语义域定义 (`SubAsync.agda`)
- [x] WF不变量形式化 (`WellFormedness.agda`) 
- [x] 9条规则形式化 (`Reductions.agda`)

### Phase 2: 核心证明 (当前任务)
- [ ] 完成 `WF-preserved` 证明 (按规则分case)
- [ ] 证明 `stuck-characterization` 定理
- [ ] 添加辅助lemma (freshness, no-cycles等)

### Phase 3: 实用性验证 
- [ ] 具体例子的execution trace  
- [ ] 与OCaml实现的bisimulation
- [ ] Redex可执行语义 (找bug神器！)

## 🎲 Alternative工具建议

如果Agda太steep，考虑：

1. **PLT Redex** (强烈推荐！)
   ```racket
   (define-language sub-async
     (e ::= (async e) (future id) (+ e e) ...)
     (s ::= (ρ Φ Q)))
   
   (define step
     (--> (async e) (future fresh-id) "M-ASYNC")
     (--> (+ (future id1) (future id2)) (future fresh-id) "M-LIFT-OP"))
   
   (redex-check step property)  ; 自动找反例！
   ```

2. **K Framework** 
   - Configuration直接映射到K的cells
   - 非常适合你的 `⟨e, (ρ,Φ,Q)⟩` 风格

3. **Ott** + **Coq**
   - 从LaTeX-style规格生成Coq代码  
   - 保持slides和formalization同步

## 💡 开始建议

1. **先用Redex验证**：快速发现规则中的bug
2. **再用Agda证明**：mechanize WF preservation  
3. **与OCaml对比**：确保formalization和implementation一致

这样即使没有类型系统，也能获得很强的formal guarantee！