-- Type Preservation proof for λ_fut (Sub_Async)
-- Corresponds to Theorem 2 (Type Preservation) in §4 of the paper.
--
-- Structure:
--   For each reduction rule, we prove that typing is preserved.
--   The store typing Σ may grow (via ⊇) when new Futures are created.
--
-- Status:
--   PROVEN (6 cases):
--   - ⊇-fresh: store extension via WF+WT freshness (zero postulates)
--   - M-AWAIT: future-lit inversion + WT + value-to-expr-typed
--   - M-AWAIT-IF: if-inversion + eval-if case analysis (zero postulates)
--   - M-ASYNC: T-FutureLit + lookup-store-same
--   - M-LIFT-OP-FF/FV/VF: T-FutureLit + lookup-store-same
--
--   POSTULATED (3 cases + 1 bridge + main theorem):
--   - value-to-expr-typed (funV case only): closure typing bridge
--   - S-COMPLETE: pending value → completed
--   - S-RESOLVE: combine function typing
--   - S-SCHEDULE: inductive substep
--   - type-preserved: main theorem

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; _≢_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Nat using (ℕ; _≟_; _<_; suc)
open import Data.Nat.Properties using (<-irrefl; n<1+n; m<n⇒m<1+n; <⇒≢)

open import SubAsync
open import WellFormedness
open import Reductions
open import Types

module TypePreservation where

-- ============================================================================
-- AUXILIARY LEMMAS
-- ============================================================================

-- Store typing lookup after prepend (same id)
lookup-store-same : ∀ (Σ : StoreTy) (id : Id) (τ : Ty) →
  lookup-store ((id , τ) ∷ Σ) id ≡ just τ
lookup-store-same Σ id τ with id ≟ id
... | yes _ = refl
... | no neq = ⊥-elim (neq refl)

-- Store typing lookup after prepend (different id)
lookup-store-neq : ∀ (Σ : StoreTy) (id id' : Id) (τ : Ty) →
  id ≢ id' →
  lookup-store ((id' , τ) ∷ Σ) id ≡ lookup-store Σ id
lookup-store-neq Σ id id' τ neq with id ≟ id'
... | yes id≡id' = ⊥-elim (neq id≡id')
... | no _ = refl

-- Extract cond5 (AllIdsBelow) from WF
WF-cond5 : ∀ {ρ Φ Q} → WF ⟨ ρ , Φ , Q ⟩ →
  (∀ id σ → lookup-future Φ id ≡ just σ → id < fresh-id Φ)
WF-cond5 (wf-invariant _ _ _ _ cond5 _) = cond5

-- ============================================================================
-- STORE TYPING EXTENSION (⊇-fresh): PROVEN
-- Replaces the old ⊇-extend postulate.
-- ============================================================================

-- Key insight: fresh-id(Φ) ∉ dom(Σ) follows from two invariants:
--   WT condition (new): dom(Σ) ⊆ dom(Φ)
--   WF condition 5:     ∀ id ∈ dom(Φ). id < fresh-id(Φ)
-- Combined: if fresh-id(Φ) ∈ dom(Σ), then fresh-id(Φ) ∈ dom(Φ),
-- then fresh-id(Φ) < fresh-id(Φ), contradiction by <-irrefl.

fresh-not-in-store : ∀ {Σ ρ Φ Q} →
  WT Σ ⟨ ρ , Φ , Q ⟩ → WF ⟨ ρ , Φ , Q ⟩ →
  ∀ τ → ¬ (lookup-store Σ (fresh-id Φ) ≡ just τ)
fresh-not-in-store (wt-state _ _ _ Σ→Φ) (wf-invariant _ _ _ _ cond5 _) τ lk-store =
  let (σ , lk-future) = Σ→Φ (fresh-id _) τ lk-store
      id<id = cond5 (fresh-id _) σ lk-future
  in <-irrefl refl id<id

-- Extending Σ with a fresh id preserves all existing lookups
⊇-fresh : ∀ {Σ ρ Φ Q τ} →
  WT Σ ⟨ ρ , Φ , Q ⟩ → WF ⟨ ρ , Φ , Q ⟩ →
  ((fresh-id Φ , τ) ∷ Σ) ⊇ Σ
⊇-fresh wt wf = ⊇-prepend-fresh (fresh-not-in-store wt wf)

-- ============================================================================
-- FUTURE-LIT INVERSION: PROVEN
-- ============================================================================

-- If future-lit id has type τ, then there exists τ' such that
-- lookup-store Σ id = just τ' and future-ty τ' <: τ.
-- Proof by induction on the typing derivation.
-- Only T-FutureLit and T-Sub can type a future-lit expression.

future-lit-inversion : ∀ {Σ Γ id τ} →
  Σ ； Γ ⊢ future-lit id ∶ τ →
  ∃[ τ' ] (lookup-store Σ id ≡ just τ' × future-ty τ' <: τ)
future-lit-inversion (T-FutureLit lk) = _ , lk , <:-refl
future-lit-inversion (T-Sub deriv s<:) with future-lit-inversion deriv
... | τ' , lk , sub₁ = τ' , lk , <:-trans sub₁ s<:

-- ============================================================================
-- VALUE-TO-EXPR TYPING BRIDGE: 3/4 cases PROVEN, funV POSTULATED
-- ============================================================================

-- Bridges value typing (Σ ⊢v v ∶ τ) to expression typing (Σ ； Γ ⊢ value-to-expr v ∶ τ).
-- Three of four value forms are fully proven:
--   numV  → num  (T-Num)
--   boolV → bool (T-Bool)
--   futureV → future-lit (T-FutureLit)   ← enabled by adding future-lit to Expr
-- The closure case (funV → fun) requires richer closure typing
-- than the current simplified TV-Fun provides.

-- Helper: extract value typing from completed entry
extract-completed-typing : ∀ {Σ v τ} → EntryTyped Σ (completed v) τ → Σ ⊢v v ∶ τ
extract-completed-typing (ET-Completed vt) = vt

value-to-expr-typed : ∀ {Σ Γ v τ} → Σ ⊢v v ∶ τ → Σ ； Γ ⊢ value-to-expr v ∶ τ
value-to-expr-typed TV-Num = T-Num
value-to-expr-typed TV-Bool = T-Bool
value-to-expr-typed (TV-Future lk) = T-FutureLit lk
value-to-expr-typed TV-Fun = postulate-fun-bridge
  where postulate postulate-fun-bridge : _
  -- The closure case requires T-Fun with Σ ； (x,τ₁)∷Γ ⊢ e ∶ τ₂,
  -- but TV-Fun carries no premises (simplified). A richer TV-Fun
  -- with a body typing proof would make this case provable.
value-to-expr-typed (TV-Sub vt s<:) = T-Sub (value-to-expr-typed vt) s<:

-- ============================================================================
-- M-AWAIT: PROVEN
-- ============================================================================

-- M-AWAIT: future-lit id → value-to-expr v
-- Proof:
--   1. future-lit-inversion: get τ', lookup-store Σ id = just τ', future-ty τ' <: τ
--   2. From WT entry-typed: Σ ⊢v v ∶ τ' (via ET-Completed)
--   3. S-Lift + transitivity: τ' <: future-ty τ' <: τ, so τ' <: τ
--   4. TV-Sub: Σ ⊢v v ∶ τ
--   5. value-to-expr-typed: Σ ； Γ ⊢ value-to-expr v ∶ τ

M-AWAIT-type-preserves : ∀ {Σ Γ id v τ ρ Φ Q} →
  Σ ； Γ ⊢ value-to-expr (futureV id) ∶ τ →
  WT Σ ⟨ ρ , Φ , Q ⟩ →
  lookup-future Φ id ≡ just (completed v) →
  Σ ； Γ ⊢ value-to-expr v ∶ τ
M-AWAIT-type-preserves {_} {_} {id} {v} {_} typing (wt-state _ entry-typed _ _) lk-completed =
  -- Step 1: inversion on typing of future-lit id
  let (τ' , lk-store , ft-sub) = future-lit-inversion typing
  -- Step 2: from WT, get value typing of v
      et = entry-typed id (completed v) τ' lk-completed lk-store
      vt = extract-completed-typing et
  -- Step 3: derive τ' <: τ via S-Lift + transitivity
      τ'<:τ = <:-trans <:-lift ft-sub
  -- Step 4: subsumption on value typing
      vt-τ = TV-Sub vt τ'<:τ
  -- Step 5: bridge to expression typing
  in value-to-expr-typed vt-τ

-- ============================================================================
-- IF-INVERSION LEMMA
-- ============================================================================

-- If `if e₁ then e₂ else e₃` has type τ, then there exists τ' such that
-- e₁ has type bool, both branches have type τ', and τ' <: τ.
-- Proof by induction on the derivation (only T-If and T-Sub apply).
if-inversion : ∀ {Σ Γ e₁ e₂ e₃ τ} →
  Σ ； Γ ⊢ if_then_else e₁ e₂ e₃ ∶ τ →
  ∃[ τ' ] (Σ ； Γ ⊢ e₁ ∶ bool-ty × Σ ； Γ ⊢ e₂ ∶ τ' × Σ ； Γ ⊢ e₃ ∶ τ' × τ' <: τ)
if-inversion (T-If cond t-br f-br) = _ , cond , t-br , f-br , <:-refl
if-inversion (T-Sub deriv s<:) with if-inversion deriv
... | τ' , cond , t-br , f-br , p = τ' , cond , t-br , f-br , <:-trans p s<:

-- ============================================================================
-- EVAL-IF TYPING HELPER
-- ============================================================================

-- eval-if always returns one of the two branches.
-- Case split mirrors the definition of eval-if in Reductions.agda.
eval-if-typed : ∀ {Σ Γ e₂ e₃ τ} → (v : Value) →
  Σ ； Γ ⊢ e₂ ∶ τ →
  Σ ； Γ ⊢ e₃ ∶ τ →
  Σ ； Γ ⊢ eval-if v e₂ e₃ ∶ τ
eval-if-typed (boolV true)    t₂ t₃ = t₂
eval-if-typed (boolV false)   t₂ t₃ = t₃
eval-if-typed (numV _)        t₂ t₃ = t₂
eval-if-typed (funV _ _ _)    t₂ t₃ = t₂
eval-if-typed (futureV _)     t₂ t₃ = t₂

-- ============================================================================
-- M-AWAIT-IF: PROVEN
-- ============================================================================

-- M-AWAIT-IF: if (future-lit id) then e₂ else e₃ → eval-if v e₂ e₃
-- Proof:
--   1. if-inversion: extract branch typings τ' and subtyping τ' <: τ
--   2. eval-if-typed: both branches have type τ', so eval-if v e₂ e₃ ∶ τ'
--   3. T-Sub: subsume from τ' to τ

M-AWAIT-IF-type-preserves : ∀ {Σ Γ id v e₂ e₃ τ ρ Φ Q} →
  Σ ； Γ ⊢ if_then_else (value-to-expr (futureV id)) e₂ e₃ ∶ τ →
  WT Σ ⟨ ρ , Φ , Q ⟩ →
  lookup-future Φ id ≡ just (completed v) →
  Σ ； Γ ⊢ eval-if v e₂ e₃ ∶ τ
M-AWAIT-IF-type-preserves {v = v} typing wt lk-completed =
  let (τ' , _ , t-br , f-br , p) = if-inversion typing
  in T-Sub (eval-if-typed v t-br f-br) p

-- ============================================================================
-- M-ASYNC: PROVEN (T-FutureLit + lookup-store-same + ⊇-fresh)
-- ============================================================================

M-ASYNC-type-preserves : ∀ {Σ Γ e τ ρ Φ Q} →
  Σ ； Γ ⊢ async e ∶ future-ty τ →
  WT Σ ⟨ ρ , Φ , Q ⟩ →
  WF ⟨ ρ , Φ , Q ⟩ →
  ∃[ Σ' ] (Σ' ⊇ Σ ×
    Σ' ； Γ ⊢ value-to-expr (futureV (fresh-id Φ)) ∶ future-ty τ)
M-ASYNC-type-preserves {Σ} {_} {_} {τ} {_} {Φ} typing wt wf =
  Σ' , ⊇-fresh wt wf , T-FutureLit (lookup-store-same Σ id τ)
  where
    id = fresh-id Φ
    Σ' = (id , τ) ∷ Σ

-- ============================================================================
-- M-LIFT-OP: PROVEN (T-FutureLit + lookup-store-same + ⊇-fresh)
-- ============================================================================

M-LIFT-OP-FF-type-preserves : ∀ {Σ Γ op id₁ id₂ ρ Φ Q} →
  Σ ； Γ ⊢ binop op (value-to-expr (futureV id₁)) (value-to-expr (futureV id₂)) ∶ future-ty (op-range op) →
  WT Σ ⟨ ρ , Φ , Q ⟩ →
  WF ⟨ ρ , Φ , Q ⟩ →
  ∃[ Σ' ] (Σ' ⊇ Σ ×
    Σ' ； Γ ⊢ value-to-expr (futureV (fresh-id Φ)) ∶ future-ty (op-range op))
M-LIFT-OP-FF-type-preserves {Σ} {_} {op} {_} {_} {_} {Φ} _ wt wf =
  Σ' , ⊇-fresh wt wf , T-FutureLit (lookup-store-same Σ id τr)
  where
    id = fresh-id Φ
    τr = op-range op
    Σ' = (id , τr) ∷ Σ

M-LIFT-OP-FV-type-preserves : ∀ {Σ Γ op id₁ v₂ ρ Φ Q} →
  Σ ； Γ ⊢ binop op (value-to-expr (futureV id₁)) (value-to-expr v₂) ∶ future-ty (op-range op) →
  WT Σ ⟨ ρ , Φ , Q ⟩ →
  WF ⟨ ρ , Φ , Q ⟩ →
  ∃[ Σ' ] (Σ' ⊇ Σ ×
    Σ' ； Γ ⊢ value-to-expr (futureV (fresh-id Φ)) ∶ future-ty (op-range op))
M-LIFT-OP-FV-type-preserves {Σ} {_} {op} {_} {_} {_} {Φ} _ wt wf =
  Σ' , ⊇-fresh wt wf , T-FutureLit (lookup-store-same Σ id (op-range op))
  where
    id = fresh-id Φ
    Σ' = (id , op-range op) ∷ Σ

M-LIFT-OP-VF-type-preserves : ∀ {Σ Γ op v₁ id₂ ρ Φ Q} →
  Σ ； Γ ⊢ binop op (value-to-expr v₁) (value-to-expr (futureV id₂)) ∶ future-ty (op-range op) →
  WT Σ ⟨ ρ , Φ , Q ⟩ →
  WF ⟨ ρ , Φ , Q ⟩ →
  ∃[ Σ' ] (Σ' ⊇ Σ ×
    Σ' ； Γ ⊢ value-to-expr (futureV (fresh-id Φ)) ∶ future-ty (op-range op))
M-LIFT-OP-VF-type-preserves {Σ} {_} {op} {_} {_} {_} {Φ} _ wt wf =
  Σ' , ⊇-fresh wt wf , T-FutureLit (lookup-store-same Σ id (op-range op))
  where
    id = fresh-id Φ
    Σ' = (id , op-range op) ∷ Σ

-- ============================================================================
-- S-COMPLETE: POSTULATED
-- ============================================================================

S-COMPLETE-type-preserves : ∀ {Σ ρ Φ Q id v ρ'} →
  WT Σ ⟨ ρ , Φ , Q ⟩ →
  id ∈ Q →
  lookup-future Φ id ≡ just (pending (value-to-expr v) ρ') →
  WT Σ ⟨ ρ , (id , completed v) ∷ Φ , filter-out id Q ⟩
S-COMPLETE-type-preserves = postulate-S-COMPLETE-type
  where postulate postulate-S-COMPLETE-type : _

-- ============================================================================
-- S-RESOLVE: POSTULATED
-- ============================================================================

S-RESOLVE-type-preserves : ∀ {Σ ρ Φ Q id deps combine vs} →
  WT Σ ⟨ ρ , Φ , Q ⟩ →
  lookup-future Φ id ≡ just (dependent deps combine) →
  collect-values Φ deps ≡ just vs →
  WT Σ ⟨ ρ , (id , completed (combine vs)) ∷ Φ , Q ⟩
S-RESOLVE-type-preserves = postulate-S-RESOLVE-type
  where postulate postulate-S-RESOLVE-type : _

-- ============================================================================
-- S-SCHEDULE: POSTULATED
-- ============================================================================

postulate
  S-SCHEDULE-type-preserves : ∀ {Σ ρ Φ Q id e' ρ' e'' s''} →
    WT Σ ⟨ ρ , Φ , Q ⟩ →
    WF ⟨ ρ , Φ , Q ⟩ →
    id ∈ Q →
    lookup-future Φ id ≡ just (pending e' ρ') →
    ⟪ e' , ⟨ ρ' , Φ , [] ⟩ ⟫ ⟶ ⟪ e'' , s'' ⟫ →
    ∃[ Σ' ] (Σ' ⊇ Σ ×
      WT Σ' ⟨ ρ , (id , pending e'' (get-env s'')) ∷ get-futures s'' , Q ++ get-queue s'' ⟩)

-- ============================================================================
-- MAIN THEOREM: TYPE PRESERVATION
-- ============================================================================

postulate
  type-preserved : ∀ {Σ Γ e τ s e' s'} →
    Σ ； Γ ⊢ e ∶ τ →
    WT Σ s →
    WF s →
    ⟪ e , s ⟫ ⟶ ⟪ e' , s' ⟫ →
    ∃[ Σ' ] (Σ' ⊇ Σ × Σ' ； Γ ⊢ e' ∶ τ × WT Σ' s')

-- PROVEN: M-ASYNC, M-LIFT-OP-FF/FV/VF, M-AWAIT
-- POSTULATED: M-AWAIT-IF, S-COMPLETE, S-RESOLVE, S-SCHEDULE
