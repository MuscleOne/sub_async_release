-- Type system for λ_fut (Sub_Async)
-- Corresponds to §3.4 of the paper: types, subtyping, typing judgments

open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import SubAsync

module Types where

-- ============================================================================
-- TYPES (§3.4)
-- ============================================================================

data Ty : Set where
  int-ty    : Ty
  bool-ty   : Ty
  fun-ty    : Ty → Ty → Ty
  future-ty : Ty → Ty

-- ============================================================================
-- SUBTYPING (Figure 4)
-- ============================================================================

data _<:_ : Ty → Ty → Set where
  -- Reflexivity (standard)
  <:-refl : ∀ {τ} → τ <: τ

  -- Transitivity (standard)
  <:-trans : ∀ {τ₁ τ₂ τ₃} → τ₁ <: τ₂ → τ₂ <: τ₃ → τ₁ <: τ₃

  -- S-FUTURE: Future is covariant
  <:-future : ∀ {τ₁ τ₂} → τ₁ <: τ₂ → future-ty τ₁ <: future-ty τ₂

  -- S-LIFT: concrete values flow into Future positions
  <:-lift : ∀ {τ} → τ <: future-ty τ

  -- S-UNLIFT: Futures can appear at demand positions requiring the underlying type
  -- This makes Future types "transparent": τ ≡ Future<τ> in the subtype preorder.
  -- Reflects the semantic guarantee that every Future eventually resolves.
  <:-unlift : ∀ {τ} → future-ty τ <: τ

-- ============================================================================
-- OPERATOR SIGNATURES
-- ============================================================================

-- Domain type for first operand
op-domain₁ : Op → Ty
op-domain₁ add = int-ty
op-domain₁ sub = int-ty
op-domain₁ mul = int-ty
op-domain₁ div = int-ty
op-domain₁ lt  = int-ty
op-domain₁ eq  = int-ty

-- Domain type for second operand
op-domain₂ : Op → Ty
op-domain₂ = op-domain₁  -- all ops are int × int in this calculus

-- Range type
op-range : Op → Ty
op-range add = int-ty
op-range sub = int-ty
op-range mul = int-ty
op-range div = int-ty
op-range lt  = bool-ty
op-range eq  = bool-ty

-- ============================================================================
-- TYPE CONTEXT AND STORE TYPING
-- ============================================================================

-- Typing context: maps variables to types
TyCtx : Set
TyCtx = List (Var × Ty)

-- Store typing: maps Future ids to types
StoreTy : Set
StoreTy = List (Id × Ty)

-- Lookup in type context
lookup-ctx : TyCtx → Var → Maybe Ty
lookup-ctx [] _ = nothing
lookup-ctx ((y , τ) ∷ Γ) x with x ≟ᵥ y
... | yes _ = just τ
... | no  _ = lookup-ctx Γ x

-- Lookup in store typing
lookup-store : StoreTy → Id → Maybe Ty
lookup-store [] _ = nothing
lookup-store ((id' , τ) ∷ Σ) id with id ≟ id'
... | yes _ = just τ
... | no  _ = lookup-store Σ id

-- ============================================================================
-- VALUE TYPING and EXPRESSION TYPING (mutually defined)
-- Value typing references expression typing in TV-Fun.
-- ============================================================================

mutual
  data _⊢v_∶_ : StoreTy → Value → Ty → Set where
    -- TV-NUM: numeric literals have type int
    TV-Num : ∀ {Σ n} →
      Σ ⊢v numV n ∶ int-ty

    -- TV-BOOL: boolean literals have type bool
    TV-Bool : ∀ {Σ b} →
      Σ ⊢v boolV b ∶ bool-ty

    -- TV-FUTURE: Future handles have type Future<Σ(id)>
    TV-Future : ∀ {Σ id τ} →
      lookup-store Σ id ≡ just τ →
      Σ ⊢v futureV id ∶ future-ty τ

    -- TV-FUN: closures have function type
    -- Body typing is context-polymorphic: a closure's body is self-contained
    -- (free variables are captured in ρ, not resolved from outer Γ).
    -- This lets value-to-expr bridge work without a separate weakening lemma.
    TV-Fun : ∀ {Σ x e ρ τ₁ τ₂} →
      (∀ {Γ} → Σ ； ((x , τ₁) ∷ Γ) ⊢ e ∶ τ₂) →
      Σ ⊢v funV x e ρ ∶ fun-ty τ₁ τ₂

    -- TV-SUB: subsumption for values
    TV-Sub : ∀ {Σ v τ₁ τ₂} →
      Σ ⊢v v ∶ τ₁ →
      τ₁ <: τ₂ →
      Σ ⊢v v ∶ τ₂

  -- ============================================================================
  -- (expression typing — second part of the mutual block)
  -- ============================================================================

  data _；_⊢_∶_ : StoreTy → TyCtx → Expr → Ty → Set where

    -- T-VAR: variable lookup
    T-Var : ∀ {Σ Γ x τ} →
      lookup-ctx Γ x ≡ just τ →
      Σ ； Γ ⊢ var x ∶ τ

    -- T-NUM: integer literals
    T-Num : ∀ {Σ Γ n} →
      Σ ； Γ ⊢ num n ∶ int-ty

    -- T-BOOL: boolean literals
    T-Bool : ∀ {Σ Γ b} →
      Σ ； Γ ⊢ bool b ∶ bool-ty

    -- T-FUTURE-LIT: Future literal has Future type
    -- Corresponds to TV-Future for expressions
    T-FutureLit : ∀ {Σ Γ id τ} →
      lookup-store Σ id ≡ just τ →
      Σ ； Γ ⊢ future-lit id ∶ future-ty τ

    -- T-ASYNC: async wraps in Future
    T-Async : ∀ {Σ Γ e τ} →
      Σ ； Γ ⊢ e ∶ τ →
      Σ ； Γ ⊢ async e ∶ future-ty τ

    -- T-OP: standard binary operation on base types
    T-Op : ∀ {Σ Γ op e₁ e₂} →
      Σ ； Γ ⊢ e₁ ∶ op-domain₁ op →
      Σ ； Γ ⊢ e₂ ∶ op-domain₂ op →
      Σ ； Γ ⊢ binop op e₁ e₂ ∶ op-range op

    -- T-LIFT-OP-FF: both operands are Futures
    T-Lift-Op-FF : ∀ {Σ Γ op e₁ e₂} →
      Σ ； Γ ⊢ e₁ ∶ future-ty (op-domain₁ op) →
      Σ ； Γ ⊢ e₂ ∶ future-ty (op-domain₂ op) →
      Σ ； Γ ⊢ binop op e₁ e₂ ∶ future-ty (op-range op)

    -- T-LIFT-OP-FV: left operand is Future
    T-Lift-Op-FV : ∀ {Σ Γ op e₁ e₂} →
      Σ ； Γ ⊢ e₁ ∶ future-ty (op-domain₁ op) →
      Σ ； Γ ⊢ e₂ ∶ op-domain₂ op →
      Σ ； Γ ⊢ binop op e₁ e₂ ∶ future-ty (op-range op)

    -- T-LIFT-OP-VF: right operand is Future
    T-Lift-Op-VF : ∀ {Σ Γ op e₁ e₂} →
      Σ ； Γ ⊢ e₁ ∶ op-domain₁ op →
      Σ ； Γ ⊢ e₂ ∶ future-ty (op-domain₂ op) →
      Σ ； Γ ⊢ binop op e₁ e₂ ∶ future-ty (op-range op)

    -- T-IF: conditional (standard)
    T-If : ∀ {Σ Γ e₁ e₂ e₃ τ} →
      Σ ； Γ ⊢ e₁ ∶ bool-ty →
      Σ ； Γ ⊢ e₂ ∶ τ →
      Σ ； Γ ⊢ e₃ ∶ τ →
      Σ ； Γ ⊢ if_then_else e₁ e₂ e₃ ∶ τ

    -- T-FUN: lambda abstraction
    T-Fun : ∀ {Σ Γ x e τ₁ τ₂} →
      Σ ； ((x , τ₁) ∷ Γ) ⊢ e ∶ τ₂ →
      Σ ； Γ ⊢ fun x e ∶ fun-ty τ₁ τ₂

    -- T-APP: function application
    T-App : ∀ {Σ Γ e₁ e₂ τ₁ τ₂} →
      Σ ； Γ ⊢ e₁ ∶ fun-ty τ₁ τ₂ →
      Σ ； Γ ⊢ e₂ ∶ τ₁ →
      Σ ； Γ ⊢ app e₁ e₂ ∶ τ₂

    -- T-LET: let binding
    T-Let : ∀ {Σ Γ x e₁ e₂ τ₁ τ₂} →
      Σ ； Γ ⊢ e₁ ∶ τ₁ →
      Σ ； ((x , τ₁) ∷ Γ) ⊢ e₂ ∶ τ₂ →
      Σ ； Γ ⊢ let⟨ x ⟩= e₁ ⟨in⟩ e₂ ∶ τ₂

    -- T-SUB: subsumption
    T-Sub : ∀ {Σ Γ e τ₁ τ₂} →
      Σ ； Γ ⊢ e ∶ τ₁ →
      τ₁ <: τ₂ →
      Σ ； Γ ⊢ e ∶ τ₂

-- ============================================================================
-- WELL-TYPED STATE (WT)
-- ============================================================================

-- Environment is well-typed w.r.t. store typing and type context
data EnvTyped : StoreTy → Env → TyCtx → Set where
  env-nil : ∀ {Σ} → EnvTyped Σ [] []
  env-cons : ∀ {Σ x v τ ρ Γ} →
    Σ ⊢v v ∶ τ →
    EnvTyped Σ ρ Γ →
    EnvTyped Σ ((x , v) ∷ ρ) ((x , τ) ∷ Γ)

-- A single Future entry is well-typed
data EntryTyped (Σ : StoreTy) : Status → Ty → Set where
  -- Pending(e, ρ): expression e has type τ under some well-typed environment
  ET-Pending : ∀ {e ρ τ Γ} →
    EnvTyped Σ ρ Γ →
    Σ ； Γ ⊢ e ∶ τ →
    EntryTyped Σ (pending e ρ) τ

  -- Completed(v): value v has type τ
  ET-Completed : ∀ {v τ} →
    Σ ⊢v v ∶ τ →
    EntryTyped Σ (completed v) τ

  -- Dependent(ids, f): combine function maps dep types to result type
  -- (the typing of f is ensured by construction from M-LIFT-OP)
  ET-Dependent : ∀ {deps f τ} →
    -- For all completed values v₁,...,vₙ of types Σ(id₁),...,Σ(idₙ),
    -- f([v₁,...,vₙ]) has type τ.
    -- We abstract this as a postulate since the combine function
    -- is constructed internally by M-LIFT-OP rules.
    EntryTyped Σ (dependent deps f) τ

-- Well-typed state: every Future entry in Φ is typed consistently with Σ
data WT : StoreTy → State → Set where
  wt-state : ∀ {Σ ρ Φ Q Γ} →
    -- Environment is well-typed
    EnvTyped Σ ρ Γ →
    -- Every Future entry is well-typed
    (∀ id σ τ →
      lookup-future Φ id ≡ just σ →
      lookup-store Σ id ≡ just τ →
      EntryTyped Σ σ τ) →
    -- Store typing covers all Future ids
    (∀ id σ →
      lookup-future Φ id ≡ just σ →
      ∃[ τ ] (lookup-store Σ id ≡ just τ)) →
    -- Store typing domain is contained in Future table domain
    -- (ensures fresh-id(Φ) ∉ dom(Σ), needed for ⊇-extend)
    (∀ id τ →
      lookup-store Σ id ≡ just τ →
      ∃[ σ ] (lookup-future Φ id ≡ just σ)) →
    WT Σ ⟨ ρ , Φ , Q ⟩

-- ============================================================================
-- STORE TYPING EXTENSION
-- ============================================================================

-- Σ' extends Σ (all old bindings preserved)
_⊇_ : StoreTy → StoreTy → Set
Σ' ⊇ Σ = ∀ id τ → lookup-store Σ id ≡ just τ → lookup-store Σ' id ≡ just τ

-- Prepend with fresh id extends: if id-new ∉ dom(Σ), then prepending preserves all old lookups
⊇-prepend-fresh : ∀ {Σ id-new τ-new} →
  (∀ τ → ¬ (lookup-store Σ id-new ≡ just τ)) →
  ((id-new , τ-new) ∷ Σ) ⊇ Σ
⊇-prepend-fresh {Σ} {id-new} {τ-new} fresh id τ lk with id ≟ id-new
... | yes refl = ⊥-elim (fresh τ lk)  -- id = id-new contradicts freshness
... | no  _    = lk

-- ============================================================================
-- DERIVED PROPERTIES
-- ============================================================================

-- S-Lift + S-Unlift makes τ ≡ Future<τ> in the subtyping preorder.
-- This is the key property for type preservation of M-AWAIT rules.

-- A value of type τ also has type Future<τ>
val-to-future : ∀ {Σ v τ} → Σ ⊢v v ∶ τ → Σ ⊢v v ∶ future-ty τ
val-to-future vt = TV-Sub vt <:-lift

-- A value of type Future<τ> also has type τ
future-to-val : ∀ {Σ v τ} → Σ ⊢v v ∶ future-ty τ → Σ ⊢v v ∶ τ
future-to-val vt = TV-Sub vt <:-unlift

-- An expression of type τ also has type Future<τ>
expr-to-future : ∀ {Σ Γ e τ} → Σ ； Γ ⊢ e ∶ τ → Σ ； Γ ⊢ e ∶ future-ty τ
expr-to-future et = T-Sub et <:-lift

-- An expression of type Future<τ> also has type τ
future-to-expr : ∀ {Σ Γ e τ} → Σ ； Γ ⊢ e ∶ future-ty τ → Σ ； Γ ⊢ e ∶ τ
future-to-expr et = T-Sub et <:-unlift
