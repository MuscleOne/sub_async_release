# Agda vs SLIDES_CORE_RULES.md: Discrepancies & Bugs Found

## Summary

During Agda mechanization, several **design decisions** and **potential bugs** were discovered that differ from or are underspecified in the slides.

---

## 🔴 Critical Issues (Require Slides Update)

> **2026-02-13 更新**: Issues 1-3 已在论文 sub-async.tex §3.2 中处理:
> - §3.2 明确写了 "prepend (shadowing) semantics"
> - §3.2 定义了 `fresh(Φ) ≜ |Φ|`
> - S-SCHEDULE rule 使用了 explicit merge notation
> 以下内容保留作为历史记录。

### 1. `s[id ↦ σ]` Semantics: Update vs Prepend ✅ RESOLVED in paper

**Slides say:**
```
s[id ↦ σ] ≜ (ρ, Φ[id ↦ σ], Q)
```
This notation suggests **replacement** (standard mathematical function update).

**Agda implements:**
```agda
update-future ⟨ ρ , Φ , Q ⟩ id σ = ⟨ ρ , (id , σ) ∷ Φ , Q ⟩
```
This **prepends** a new entry, allowing **duplicate IDs** in `Φ`.

**Consequence:** 
- `lookup-future` returns the **first match** (i.e., the **newest** entry)
- This works correctly because newer states shadow older ones
- But it's **different semantics** than standard function update

**Recommendation for slides:**
Either:
1. Clarify that `Φ` is a **list** (not a partial function), with newest-first shadowing
2. Or add a note: "Implementation may use list with shadowing for simplicity"

---

### 2. `fresh(Φ)` Is Underspecified ✅ RESOLVED in paper

**Slides say:**
```
fresh(Φ) ≜ choose id s.t. id ∉ dom(Φ)
```
Non-deterministic choice — any unused ID is valid.

**Agda implements:**
```agda
fresh-id : FutureTable → Id  
fresh-id [] = zero
fresh-id (_ ∷ rest) = suc (fresh-id rest)
```
Returns `length(Φ)` — **deterministic**, sequential allocation (0, 1, 2, ...).

**Consequence:**
- The slides' non-deterministic version is fine for theory
- But proofs need a **concrete** implementation
- The length-based approach guarantees freshness **only if** IDs are allocated sequentially

**Potential bug:** If `Φ` uses prepend (as above), `length(Φ)` may not be fresh when duplicates exist!

**Recommendation:**
1. State explicitly: "In implementation, `fresh(Φ) = |Φ|` assuming sequential allocation"
2. OR: Use a global counter separate from `Φ`

---

### 3. S-SCHEDULE: State Merging Semantics ✅ RESOLVED in paper

**Slides say:**
```
⟨e, s⟩ → ⟨e, (ρ, s''.Φ, Q ∪ s''.Q)[id ↦ Pending(e'', s''.ρ)]⟩
```
Uses `s''.Φ` directly (replaces original `Φ`).

**Agda implements:**
```agda
S-SCHEDULE : ... →
  ⟪ e , update-future 
         ⟨ ρ , merge-futures Φ (get-futures s'') , merge-queues Q (get-queue s'') ⟩ 
         id (pending e'' (get-env s'')) ⟫
```
Where:
```agda
merge-futures Φ₁ Φ₂ = Φ₁ ++ Φ₂
merge-queues Q₁ Q₂ = Q₁ ++ Q₂
```

**Issue in slides:**
The rule `(ρ, s''.Φ, Q ∪ s''.Q)` is **incorrect**!
- `s''.Φ` was initialized with `Φ` (from premise)
- But using `s''.Φ` directly **loses the main thread's environment `ρ`**

**Correct semantics should be:**
```
(ρ, Φ ++ newly-created-entries, Q ∪ s''.Q)
```
OR simply note that `s''.Φ` already contains original `Φ` (since substep started with it).

**Recommendation:** Clarify S-SCHEDULE more carefully, or use explicit merge notation.

---

## 🟡 Minor Issues (Clarification Needed)

### 4. `s ⊖ id` Removes ALL Occurrences

**Slides say:**
```
s ⊖ id ≜ (ρ, Φ, Q \ {id})
```
Set difference — removes one element.

**Agda implements:**
```agda
remove-from-queue : State → Id → State
remove-from-queue ⟨ ρ , Φ , Q ⟩ id = ⟨ ρ , Φ , filter-out id Q ⟩
  where
  filter-out : Id → List Id → List Id
  filter-out target (x ∷ xs) with target ≟ x  
  ... | yes _ = filter-out target xs  -- remove ALL occurrences
  ... | no  _ = x ∷ filter-out target xs
```

**Minor difference:** Filter removes ALL occurrences; set difference assumes at most one.

For correct implementation, this should be fine (WF ensures at most one), but worth noting.

---

### 5. FutureTable: Partial Function vs List

**Slides define:**
```
Φ ∈ FutureTable = Id ⇀ Status
```
Partial function notation.

**Agda implements:**
```agda
FutureTable = List (Id × Status)
```
Association list with potential duplicates.

**Recommendation:** Add a note in slides:
> "Implemented as association list; `Φ(id)` returns the first matching entry."

---

### 6. Queue: Set vs List

**Slides define:**
```
Q ∈ 𝒫(Id)
```
Set (unordered, no duplicates).

**Agda implements:**
```agda
PendingSet = List Id   -- (backward-compatible alias PendingQueue still exists)
```

**Impact:** Non-deterministic choice still models correctly (any element can be chosen), but list allows duplicates theoretically.

---

## 🟢 Verified Correct

### 7. WF Invariant Definition ✓

The 4 well-formedness conditions in slides match exactly:
1. `id ∈ Q ⟺ Φ(id) = Pending(_, _)` ✓
2. No dangling dependencies ✓
3. No self-cycles, no duplicates ✓
4. No dangling Future refs in environment ✓

### 8. State Machine Transitions ✓

| Status | Created by | Transitions to |
|--------|-----------|----------------|
| `Pending(e, ρ)` | M-ASYNC | `Completed` via S-COMPLETE |
| `Dependent(ids, f)` | M-LIFT-OP | `Completed` via S-RESOLVE |
| `Completed(v)` | S-COMPLETE, S-RESOLVE | (terminal) |

All correctly modeled in Agda.

### 9. All 9 Rules Have Verified Proofs ✓

- M-ASYNC ✓
- M-LIFT-OP-FF ✓
- M-LIFT-OP-FV ✓
- M-LIFT-OP-VF ✓
- M-AWAIT ✓
- M-AWAIT-IF ✓
- M-AWAIT-APP1 ✓
- M-AWAIT-APP2 ✓
- S-SCHEDULE ✓
- S-COMPLETE ✓
- S-RESOLVE ✓

---

## Recommended Changes to SLIDES_CORE_RULES.md

> **2026-02-13**: 以下建议已全部反映在 sub-async.tex §3.2 中。
> SLIDES_CORE_RULES.md 仍用旧 notation（可接受，因为 paper 是最终版本）。

### Section: Auxiliary Definitions — ✅ Done in paper

Paper §3.2 now defines `fresh(Φ) ≜ |Φ|` and describes prepend semantics.

### Section: Configuration — ✅ Done in paper

Paper §3.2 explicitly states "prepend (shadowing) semantics".

### Section: S-SCHEDULE — ✅ Done in paper

Paper uses explicit merge notation in the S-SCHEDULE rule.

---

## File Reference

| Issue | Slides Line | Agda File:Line |
|-------|-------------|----------------|
| `s[id ↦ σ]` | ~107 | WellFormedness.agda:86-87 |
| `fresh(Φ)` | ~90 | WellFormedness.agda:80-82 |
| S-SCHEDULE | ~183 | Reductions.agda:149-155 |
| `s ⊖ id` | ~109 | WellFormedness.agda:93-98 |
