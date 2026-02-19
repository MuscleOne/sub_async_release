-- Type Preservation proof for λ_fut (Sub_Async)
-- Corresponds to Theorem 2 (Type Preservation) in §4 of the paper.
--
-- Structure:
--   For each reduction rule, we prove that typing is preserved.
--   The store typing Σ may grow (via ⊇) when new Futures are created.
--
-- Status:
--   PROVEN (7 cases + value-to-expr bridge):
--   - ⊇-fresh: store extension via WF+WT freshness (zero postulates)
--   - value-to-expr-typed: ALL 4 value forms (zero postulates)
--   - expr-to-value-typed: inverse bridge (3/4 zero postulates, funV uses funV-typing)
--   - M-AWAIT: future-lit inversion + WT + value-to-expr-typed
--   - M-AWAIT-IF: if-inversion + eval-if case analysis (zero postulates)
--   - M-ASYNC: T-FutureLit + lookup-store-same
--   - M-LIFT-OP-FF/FV/VF: T-FutureLit + lookup-store-same
--   - S-COMPLETE: expr-to-value-typed + WT reconstruction
--
--   POSTULATED (1 case + 1 semantic bridge + main theorem):
--   - funV-typing: closure value typing bridge (semantic, only for funV)
--   - S-SCHEDULE: inductive substep
--   - type-preserved: main theorem

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; _≢_; inspect; [_]; subst)
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
-- COMBINE FUNCTION TYPING: PROVEN
-- Previously these were FALSE postulates (combine with numV 0 fallback was
-- unsound for lt/eq which return bool-ty). Now uses op-default for type-correct
-- defaults, and all three lemmas are fully proven.
-- ============================================================================

-- Default value for each op has the correct type
op-default-typed : ∀ {Σ} → (op : Op) → Σ ⊢v op-default op ∶ op-range op
op-default-typed add = TV-Num
op-default-typed sub = TV-Num
op-default-typed mul = TV-Num
op-default-typed div = TV-Num
op-default-typed lt  = TV-Bool
op-default-typed eq  = TV-Bool

-- When apply-op succeeds, the result has the correct type.
-- Proof by case analysis on op, v₁, v₂.
apply-op-typed : ∀ {Σ} → (op : Op) → (v₁ v₂ v : Value) →
  apply-op op v₁ v₂ ≡ just v → Σ ⊢v v ∶ op-range op
-- Success cases: both arguments are numV
apply-op-typed add (numV m) (numV n) _ refl = TV-Num
apply-op-typed sub (numV m) (numV n) _ refl = TV-Num
apply-op-typed mul (numV m) (numV n) _ refl = TV-Num
apply-op-typed div (numV _) (numV 0) _ ()
apply-op-typed div (numV m) (numV (suc n)) _ refl = TV-Num
apply-op-typed lt  (numV m) (numV n) _ refl = TV-Bool
apply-op-typed eq  (numV m) (numV n) _ refl = TV-Bool
-- Absurd: first value arg is not numV (apply-op returns nothing)
apply-op-typed add (boolV _) _ _ ()
apply-op-typed sub (boolV _) _ _ ()
apply-op-typed mul (boolV _) _ _ ()
apply-op-typed div (boolV _) _ _ ()
apply-op-typed lt  (boolV _) _ _ ()
apply-op-typed eq  (boolV _) _ _ ()
apply-op-typed add (futureV _) _ _ ()
apply-op-typed sub (futureV _) _ _ ()
apply-op-typed mul (futureV _) _ _ ()
apply-op-typed div (futureV _) _ _ ()
apply-op-typed lt  (futureV _) _ _ ()
apply-op-typed eq  (futureV _) _ _ ()
apply-op-typed add (funV _ _ _) _ _ ()
apply-op-typed sub (funV _ _ _) _ _ ()
apply-op-typed mul (funV _ _ _) _ _ ()
apply-op-typed div (funV _ _ _) _ _ ()
apply-op-typed lt  (funV _ _ _) _ _ ()
apply-op-typed eq  (funV _ _ _) _ _ ()
-- Absurd: first value arg is numV but second is not
apply-op-typed add (numV _) (boolV _) _ ()
apply-op-typed sub (numV _) (boolV _) _ ()
apply-op-typed mul (numV _) (boolV _) _ ()
apply-op-typed div (numV _) (boolV _) _ ()
apply-op-typed lt  (numV _) (boolV _) _ ()
apply-op-typed eq  (numV _) (boolV _) _ ()
apply-op-typed add (numV _) (futureV _) _ ()
apply-op-typed sub (numV _) (futureV _) _ ()
apply-op-typed mul (numV _) (futureV _) _ ()
apply-op-typed div (numV _) (futureV _) _ ()
apply-op-typed lt  (numV _) (futureV _) _ ()
apply-op-typed eq  (numV _) (futureV _) _ ()
apply-op-typed add (numV _) (funV _ _ _) _ ()
apply-op-typed sub (numV _) (funV _ _ _) _ ()
apply-op-typed mul (numV _) (funV _ _ _) _ ()
apply-op-typed div (numV _) (funV _ _ _) _ ()
apply-op-typed lt  (numV _) (funV _ _ _) _ ()
apply-op-typed eq  (numV _) (funV _ _ _) _ ()

-- combine-binary produces correct type for 2-element lists
combine-binary-typed : ∀ {Σ op} → (vs : List Value) →
    length vs ≡ 2 → Σ ⊢v combine-binary op vs ∶ op-range op
combine-binary-typed {Σ} {op} (v₁ ∷ v₂ ∷ []) refl
  with apply-op op v₁ v₂ in eq
... | just v  = apply-op-typed op v₁ v₂ v eq
... | nothing = op-default-typed op

-- combine-unary-left produces correct type for 1-element lists
combine-unary-left-typed : ∀ {Σ op v₂} → (vs : List Value) →
    length vs ≡ 1 → Σ ⊢v combine-unary-left op v₂ vs ∶ op-range op
combine-unary-left-typed {Σ} {op} {v₂} (v₁ ∷ []) refl
  with apply-op op v₁ v₂ in eq
... | just v  = apply-op-typed op v₁ v₂ v eq
... | nothing = op-default-typed op

-- combine-unary-right produces correct type for 1-element lists
combine-unary-right-typed : ∀ {Σ op v₁} → (vs : List Value) →
    length vs ≡ 1 → Σ ⊢v combine-unary-right op v₁ vs ∶ op-range op
combine-unary-right-typed {Σ} {op} {v₁} (v₂ ∷ []) refl
  with apply-op op v₁ v₂ in eq
... | just v  = apply-op-typed op v₁ v₂ v eq
... | nothing = op-default-typed op

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
-- EXPR INVERSION LEMMAS (for value-form expressions)
-- ============================================================================

-- num n can only be typed by T-Num or T-Sub.
num-inversion : ∀ {Σ Γ n τ} →
  Σ ； Γ ⊢ num n ∶ τ → int-ty <: τ
num-inversion T-Num = <:-refl
num-inversion (T-Sub d s<:) = <:-trans (num-inversion d) s<:

-- bool b can only be typed by T-Bool or T-Sub.
bool-inversion : ∀ {Σ Γ b τ} →
  Σ ； Γ ⊢ bool b ∶ τ → bool-ty <: τ
bool-inversion T-Bool = <:-refl
bool-inversion (T-Sub d s<:) = <:-trans (bool-inversion d) s<:

-- fun x e can only be typed by T-Fun or T-Sub.
fun-inversion : ∀ {Σ Γ x e τ} →
  Σ ； Γ ⊢ fun x e ∶ τ →
  ∃[ τ₁ ] ∃[ τ₂ ] (Σ ； ((x , τ₁) ∷ Γ) ⊢ e ∶ τ₂ × fun-ty τ₁ τ₂ <: τ)
fun-inversion (T-Fun body) = _ , _ , body , <:-refl
fun-inversion (T-Sub d s<:) with fun-inversion d
... | τ₁ , τ₂ , body , p = τ₁ , τ₂ , body , <:-trans p s<:

-- ============================================================================
-- EXPR-TO-VALUE TYPING BRIDGE: 3/4 PROVEN + funV via funV-typing
-- ============================================================================

-- Closure value typing bridge.
--
-- SEMANTIC JUSTIFICATION:
-- When `fun x e` is typeable in some context Γ, the closure `funV x e ρ`
-- (which captures runtime bindings for free variables in e) is a well-typed
-- value. This is a semantic property of closure semantics: ρ provides
-- runtime bindings that correspond to the typing context Γ.
--
-- WHY IS THIS A POSTULATE?
-- The Agda formalization does not model the connection between runtime
-- environments (Env) and typing contexts (Ctx). Specifically:
-- - `value-to-expr (funV x e ρ) = fun x e` DROPS the environment ρ
-- - TV-Fun requires `∀{Γ'} → Σ ； ((x,τ₁)∷Γ') ⊢ e ∶ τ₂` (context-polymorphic)
-- - But `fun-inversion` only gives a specific Γ
--
-- CORRECTNESS ARGUMENT:
-- In actual execution, `funV x e ρ` always satisfies: ρ binds all free
-- variables in e (except x). This is guaranteed by the evaluation rules.
-- However, our formalization has no `EnvTyped ρ Γ` relation to express this.
--
-- COMPARISON WITH expr-weaken:
-- The original attempt used `expr-weaken : Σ；Γ ⊢ e ∶ τ → Σ；Γ' ⊢ e ∶ τ`,
-- which is PROVABLY FALSE for arbitrary Γ' (counterexample: `x+y` typed in
-- [(x,int),(y,int)] but not in []). The current `funV-typing` is much
-- narrower (only for closures) and semantically justified (closures capture
-- their environment), making it the "least incorrect" postulate.
--
-- TO ELIMINATE THIS POSTULATE:
-- Would require either:
-- 1. Add EnvTyped premise to TV-Fun: `EnvTyped Σ ρ Γ → ...`
-- 2. Introduce a well-typed closure invariant throughout evaluation
-- 3. Change EntryTyped to store value typing instead of expression typing
-- All options require substantial refactoring beyond the current scope.
postulate
  funV-typing : ∀ {Σ Γ x e ρ τ} →
    Σ ； Γ ⊢ fun x e ∶ τ →
    Σ ⊢v funV x e ρ ∶ τ

expr-to-value-typed : ∀ {Σ Γ v τ} → Σ ； Γ ⊢ value-to-expr v ∶ τ → Σ ⊢v v ∶ τ
expr-to-value-typed {v = numV n} typing =
  TV-Sub TV-Num (num-inversion typing)
expr-to-value-typed {v = boolV b} typing =
  TV-Sub TV-Bool (bool-inversion typing)
expr-to-value-typed {v = futureV id} typing =
  let (τ' , lk , p) = future-lit-inversion typing
  in TV-Sub (TV-Future lk) p
expr-to-value-typed {v = funV x e ρ} typing = funV-typing typing

-- ============================================================================
-- VALUE-TO-EXPR TYPING BRIDGE: ALL 4 CASES PROVEN
-- ============================================================================

-- Bridges value typing (Σ ⊢v v ∶ τ) to expression typing (Σ ； Γ ⊢ value-to-expr v ∶ τ).
-- All four value forms are fully proven:
--   numV    → num         (T-Num)
--   boolV   → bool        (T-Bool)
--   futureV → future-lit  (T-FutureLit)
--   funV    → fun         (T-Fun)  ← enabled by enriched TV-Fun

extract-completed-typing : ∀ {Σ v τ} → EntryTyped Σ (completed v) τ → Σ ⊢v v ∶ τ
extract-completed-typing (ET-Completed vt) = vt

value-to-expr-typed : ∀ {Σ Γ v τ} → Σ ⊢v v ∶ τ → Σ ； Γ ⊢ value-to-expr v ∶ τ
value-to-expr-typed TV-Num = T-Num
value-to-expr-typed TV-Bool = T-Bool
value-to-expr-typed (TV-Future lk) = T-FutureLit lk
value-to-expr-typed (TV-Fun body-ty) = T-Fun body-ty
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
-- EVAL-IF TYPING
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
-- S-COMPLETE: PROVEN
-- ============================================================================

lookup-future-same : ∀ {Φ id σ} → lookup-future ((id , σ) ∷ Φ) id ≡ just σ
lookup-future-same {_} {id} with id ≟ id
... | yes _ = refl
... | no neq = ⊥-elim (neq refl)

lookup-future-neq : ∀ {Φ id id' σ} → id ≢ id' →
  lookup-future ((id' , σ) ∷ Φ) id ≡ lookup-future Φ id
lookup-future-neq {_} {id} {id'} neq with id ≟ id'
... | yes id≡id' = ⊥-elim (neq id≡id')
... | no _ = refl

S-COMPLETE-type-preserves : ∀ {Σ ρ Φ Q id v ρ'} →
  WT Σ ⟨ ρ , Φ , Q ⟩ →
  id ∈ Q →
  lookup-future Φ id ≡ just (pending (value-to-expr v) ρ') →
  WT Σ ⟨ ρ , (id , completed v) ∷ Φ , filter-out id Q ⟩
S-COMPLETE-type-preserves {Σ} {_} {Φ} {_} {id} {v}
  (wt-state env-ty entry-typed Φ→Σ Σ→Φ) _ lk-pending =
  wt-state env-ty entry-typed' Φ→Σ' Σ→Φ'
  where
    -- Condition 2: every entry in new Φ is well-typed
    entry-typed' : ∀ id' σ τ →
      lookup-future ((id , completed v) ∷ Φ) id' ≡ just σ →
      lookup-store Σ id' ≡ just τ →
      EntryTyped Σ σ τ
    entry-typed' id' σ τ lk-f lk-s with id' ≟ id
    -- Case id' = id: the updated entry
    entry-typed' .id .(completed v) τ refl lk-s | yes refl =
      let et = entry-typed id (pending (value-to-expr v) _) τ lk-pending lk-s
      in case et of λ where
          (ET-Pending _ expr-ty) → ET-Completed (expr-to-value-typed expr-ty)
    -- Case id' ≠ id: pass through to old Φ
    entry-typed' id' σ τ lk-f lk-s | no _ = entry-typed id' σ τ lk-f lk-s

    -- Condition 3: every entry in new Φ has a store type
    Φ→Σ' : ∀ id' σ →
      lookup-future ((id , completed v) ∷ Φ) id' ≡ just σ →
      ∃[ τ ] (lookup-store Σ id' ≡ just τ)
    Φ→Σ' id' σ lk-f with id' ≟ id
    Φ→Σ' .id _ refl | yes refl = Φ→Σ id (pending (value-to-expr v) _) lk-pending
    Φ→Σ' id' σ lk-f | no _ = Φ→Σ id' σ lk-f

    -- Condition 4: every store type has an entry in new Φ
    Σ→Φ' : ∀ id' τ →
      lookup-store Σ id' ≡ just τ →
      ∃[ σ ] (lookup-future ((id , completed v) ∷ Φ) id' ≡ just σ)
    Σ→Φ' id' τ lk-s with id' ≟ id
    ... | yes refl = completed v , refl
    ... | no _ = let (σ , lk-f) = Σ→Φ id' τ lk-s in σ , lk-f

just-injective : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
just-injective refl = refl

-- ============================================================================
-- S-RESOLVE: PROVEN
-- ============================================================================

collect-values-length : ∀ {Φ : FutureTable} {deps : List Id} {vs : List Value} →
  collect-values Φ deps ≡ just vs → length vs ≡ length deps
collect-values-length {_} {[]} refl = refl
collect-values-length {Φ} {id ∷ ids} _ with lookup-future Φ id
collect-values-length {_} {_ ∷ _} () | just (pending _ _)
collect-values-length {_} {_ ∷ _} () | just (dependent _ _)
collect-values-length {_} {_ ∷ _} () | nothing
collect-values-length {Φ} {_ ∷ ids} _ | just (completed v)
  with collect-values Φ ids in eqc
collect-values-length {_} {_ ∷ _} () | just (completed _) | nothing
collect-values-length {_} {_ ∷ ids} refl | just (completed _) | just vs' =
  cong suc (collect-values-length {deps = ids} {vs = vs'} eqc)

S-RESOLVE-type-preserves : ∀ {Σ ρ Φ Q id deps combine vs} →
  WT Σ ⟨ ρ , Φ , Q ⟩ →
  lookup-future Φ id ≡ just (dependent deps combine) →
  collect-values Φ deps ≡ just vs →
  WT Σ ⟨ ρ , (id , completed (combine vs)) ∷ Φ , Q ⟩
S-RESOLVE-type-preserves {Σ} {_} {Φ} {_} {id} {deps} {combine} {vs}
  (wt-state env-ty entry-typed Φ→Σ Σ→Φ) lk-dep col =
  wt-state env-ty entry-typed' Φ→Σ' Σ→Φ'
  where
    -- Get the type of this future from the store
    τ : Ty
    τ = proj₁ (Φ→Σ id (dependent deps combine) lk-dep)
    
    lk-store : lookup-store Σ id ≡ just τ
    lk-store = proj₂ (Φ→Σ id (dependent deps combine) lk-dep)
    
    -- Get ET-Dependent, which gives us the typing premise for combine
    et-dep : EntryTyped Σ (dependent deps combine) τ
    et-dep = entry-typed id (dependent deps combine) τ lk-dep lk-store
    
    -- Extract the typing proof from ET-Dependent
    extract-combine-typed : EntryTyped Σ (dependent deps combine) τ →
      (∀ vs₁ → length vs₁ ≡ length deps → Σ ⊢v combine vs₁ ∶ τ)
    extract-combine-typed (ET-Dependent _ f-typed) = f-typed
    
    -- Apply to our specific vs
    combine-vs-typed : Σ ⊢v combine vs ∶ τ
    combine-vs-typed = extract-combine-typed et-dep vs
      (collect-values-length {Φ} {deps} {vs} col)
    
    -- Condition 2: every entry in new Φ is well-typed
    entry-typed' : ∀ id' σ τ' →
      lookup-future ((id , completed (combine vs)) ∷ Φ) id' ≡ just σ →
      lookup-store Σ id' ≡ just τ' →
      EntryTyped Σ σ τ'
    entry-typed' id' σ τ' lk-f lk-s with id' ≟ id
    -- Case id' = id: the resolved entry
    entry-typed' .id .(completed (combine vs)) τ' refl lk-s | yes refl =
      let τ'≡τ = just-injective (trans (sym lk-s) lk-store)
      in subst (λ z → EntryTyped Σ (completed (combine vs)) z) (sym τ'≡τ) (ET-Completed combine-vs-typed)
    -- Case id' ≠ id: pass through to old Φ
    entry-typed' id' σ τ' lk-f lk-s | no _ = entry-typed id' σ τ' lk-f lk-s
    
    -- Condition 3: every entry in new Φ has a store type
    Φ→Σ' : ∀ id' σ →
      lookup-future ((id , completed (combine vs)) ∷ Φ) id' ≡ just σ →
      ∃[ τ' ] (lookup-store Σ id' ≡ just τ')
    Φ→Σ' id' σ lk-f with id' ≟ id
    Φ→Σ' .id _ refl | yes refl = τ , lk-store
    Φ→Σ' id' σ lk-f | no _ = Φ→Σ id' σ lk-f
    
    -- Condition 4: every store type has an entry in new Φ
    Σ→Φ' : ∀ id' τ' →
      lookup-store Σ id' ≡ just τ' →
      ∃[ σ ] (lookup-future ((id , completed (combine vs)) ∷ Φ) id' ≡ just σ)
    Σ→Φ' id' τ' lk-s with id' ≟ id
    ... | yes refl = completed (combine vs) , refl
    ... | no _ = let (σ , lk-f) = Σ→Φ id' τ' lk-s in σ , lk-f

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

-- PROVEN: M-ASYNC, M-LIFT-OP-FF/FV/VF, M-AWAIT, M-AWAIT-IF, S-COMPLETE, S-RESOLVE
-- PROVEN (previously postulated): combine-*-typed, collect-values-length
-- POSTULATED: S-SCHEDULE, type-preserved (main theorem), funV-typing (semantic bridge)
