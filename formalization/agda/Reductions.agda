-- Operational semantics reduction rules
-- The 9 core rules from SLIDES_CORE_RULES.md

open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Maybe using (Maybe; nothing; just)  
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _+_; _*_; _∸_; _<ᵇ_; _≡ᵇ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)

open import SubAsync
open import WellFormedness

module Reductions where

apply-op : Op → Value → Value → Maybe Value
apply-op add (numV m) (numV n) = just (numV (m + n))
apply-op sub (numV m) (numV n) = just (numV (m ∸ n)) 
apply-op mul (numV m) (numV n) = just (numV (m * n))
apply-op div (numV m) (numV 0) = nothing  -- division by zero
apply-op div (numV m) (numV n) = just (numV (m / n))  -- postulate division
  where postulate _/_ : ℕ → ℕ → ℕ
apply-op lt  (numV m) (numV n) = just (boolV (m <ᵇ n))  
apply-op eq  (numV m) (numV n) = just (boolV (m ≡ᵇ n))
apply-op _ _ _ = nothing  -- type mismatch

-- Default value for each operator (type-correct fallback)
-- Returns a value whose type matches op-range op.
op-default : Op → Value
op-default add = numV 0
op-default sub = numV 0
op-default mul = numV 0
op-default div = numV 0
op-default lt  = boolV false
op-default eq  = boolV false

combine-binary : Op → List Value → Value  
combine-binary op (v₁ ∷ v₂ ∷ []) with apply-op op v₁ v₂
... | just v = v
... | nothing = op-default op
combine-binary op _ = op-default op

combine-unary-left : Op → Value → List Value → Value
combine-unary-left op v₂ (v₁ ∷ []) with apply-op op v₁ v₂  
... | just v = v
... | nothing = op-default op
combine-unary-left op v₂ _ = op-default op

combine-unary-right : Op → Value → List Value → Value  
combine-unary-right op v₁ (v₂ ∷ []) with apply-op op v₁ v₂
... | just v = v  
... | nothing = op-default op
combine-unary-right op v₁ _ = op-default op

-- Postulated: requires full λ-calculus substitution
postulate eval-app : Value → Expr → Expr
postulate eval-app-val : Value → Value → Expr

eval-if : Value → Expr → Expr → Expr
eval-if (boolV true) e₂ e₃ = e₂
eval-if (boolV false) e₂ e₃ = e₃  
eval-if _ e₂ e₃ = e₂

-- Convert Value back to Expr (for M-AWAIT)
value-to-expr : Value → Expr
value-to-expr (numV n) = num n
value-to-expr (boolV b) = bool b
value-to-expr (futureV id) = future-lit id
value-to-expr (funV x e ρ) = fun x e

collect-values : Future-table → List Id → Maybe (List Value)
collect-values Φ [] = just []
collect-values Φ (id ∷ ids) with lookup-future Φ id
collect-values Φ (id ∷ ids) | just (completed v) with collect-values Φ ids
collect-values Φ (id ∷ ids) | just (completed v) | just vs = just (v ∷ vs)
collect-values Φ (id ∷ ids) | just (completed v) | nothing = nothing
collect-values Φ (id ∷ ids) | just (pending _ _) = nothing  
collect-values Φ (id ∷ ids) | just (dependent _ _) = nothing  
collect-values Φ (id ∷ ids) | nothing = nothing

all-completed : Future-table → List Id → Bool
all-completed Φ [] = true
all-completed Φ (id ∷ ids) with lookup-future Φ id
... | just (completed _) = all-completed Φ ids
... | _ = false

merge-futures : Future-table → Future-table → Future-table
merge-futures Φ₁ Φ₂ = Φ₁ ++ Φ₂

merge-queues : Pending-set → Pending-set → Pending-set  
merge-queues Q₁ Q₂ = Q₁ ++ Q₂

-- REDUCTION RELATION  
-- ⟨e, s⟩ → ⟨e', s'⟩
data _⟶_ : Configuration → Configuration → Set where

  -- M-ASYNC: async e → Future(id), add to pending
  M-ASYNC : ∀ {e ρ Φ Q} →
    let id = fresh-id Φ in
    let s' = update-future (add-to-queue ⟨ ρ , Φ , Q ⟩ id) id (pending e ρ) in
    ⟪ async e , ⟨ ρ , Φ , Q ⟩ ⟫ ⟶ ⟪ value-to-expr (futureV id) , s' ⟫

  -- M-LIFT-OP-FF: Future op Future → new Dependent Future  
  M-LIFT-OP-FF : ∀ {op id₁ id₂ ρ Φ Q} →
    id-in-domain id₁ Φ →
    id-in-domain id₂ Φ →
    id₁ ≢ id₂ →
    let id = fresh-id Φ in
    let s' = update-future ⟨ ρ , Φ , Q ⟩ id (dependent (id₁ ∷ id₂ ∷ []) (combine-binary op)) in
    ⟪ binop op (value-to-expr (futureV id₁)) (value-to-expr (futureV id₂)) , ⟨ ρ , Φ , Q ⟩ ⟫ ⟶ 
    ⟪ value-to-expr (futureV id) , s' ⟫

  -- M-LIFT-OP-FV: Future op Value → new Dependent Future
  M-LIFT-OP-FV : ∀ {op id₁ v₂ ρ Φ Q} →  
    id-in-domain id₁ Φ →
    let id = fresh-id Φ in
    let s' = update-future ⟨ ρ , Φ , Q ⟩ id (dependent (id₁ ∷ []) (combine-unary-left op v₂)) in
    ⟪ binop op (value-to-expr (futureV id₁)) (value-to-expr v₂) , ⟨ ρ , Φ , Q ⟩ ⟫ ⟶ 
    ⟪ value-to-expr (futureV id) , s' ⟫

  -- M-LIFT-OP-VF: Value op Future → new Dependent Future  
  M-LIFT-OP-VF : ∀ {op v₁ id₂ ρ Φ Q} →
    id-in-domain id₂ Φ →
    let id = fresh-id Φ in  
    let s' = update-future ⟨ ρ , Φ , Q ⟩ id (dependent (id₂ ∷ []) (combine-unary-right op v₁)) in  
    ⟪ binop op (value-to-expr v₁) (value-to-expr (futureV id₂)) , ⟨ ρ , Φ , Q ⟩ ⟫ ⟶
    ⟪ value-to-expr (futureV id) , s' ⟫

  -- M-AWAIT: Extract value from completed Future
  M-AWAIT : ∀ {id v ρ Φ Q} →
    lookup-future Φ id ≡ just (completed v) →
    ⟪ value-to-expr (futureV id) , ⟨ ρ , Φ , Q ⟩ ⟫ ⟶ ⟪ value-to-expr v , ⟨ ρ , Φ , Q ⟩ ⟫

  -- M-AWAIT-IF: Await in if condition
  M-AWAIT-IF : ∀ {id v e₂ e₃ ρ Φ Q} →
    lookup-future Φ id ≡ just (completed v) →  
    ⟪ if (value-to-expr (futureV id)) then e₂ else e₃ , ⟨ ρ , Φ , Q ⟩ ⟫ ⟶ 
    ⟪ eval-if v e₂ e₃ , ⟨ ρ , Φ , Q ⟩ ⟫

  -- M-AWAIT-APP1: Await function in application
  M-AWAIT-APP1 : ∀ {id v e ρ Φ Q} →
    lookup-future Φ id ≡ just (completed v) →
    ⟪ app (value-to-expr (futureV id)) e , ⟨ ρ , Φ , Q ⟩ ⟫ ⟶ 
    ⟪ eval-app v e , ⟨ ρ , Φ , Q ⟩ ⟫

  -- M-AWAIT-APP2: Await argument in application  
  M-AWAIT-APP2 : ∀ {v id v' ρ Φ Q} →
    lookup-future Φ id ≡ just (completed v') →
    ⟪ app (value-to-expr v) (value-to-expr (futureV id)) , ⟨ ρ , Φ , Q ⟩ ⟫ ⟶
    ⟪ eval-app-val v v' , ⟨ ρ , Φ , Q ⟩ ⟫

  -- S-SCHEDULE: Execute one step of pending Future
  -- Result uses s''.Φ directly (already extends Φ since substep starts from Φ)
  S-SCHEDULE : ∀ {e ρ Φ Q id e' ρ' e'' s''} →
    id ∈Q Q →
    lookup-future Φ id ≡ just (pending e' ρ') →  
    ⟪ e' , ⟨ ρ' , Φ , [] ⟩ ⟫ ⟶ ⟪ e'' , s'' ⟫ →
    ⟪ e , ⟨ ρ , Φ , Q ⟩ ⟫ ⟶ 
    ⟪ e , update-future ⟨ ρ , get-futures s'' , Q ++ get-queue s'' ⟩ 
           id (pending e'' (get-env s'')) ⟫

  -- S-COMPLETE: Pending → Completed when expression is value
  S-COMPLETE : ∀ {e ρ Φ Q id v ρ'} →  
    id ∈Q Q →
    lookup-future Φ id ≡ just (pending (value-to-expr v) ρ') →
    ⟪ e , ⟨ ρ , Φ , Q ⟩ ⟫ ⟶  
    ⟪ e , update-future (remove-from-queue ⟨ ρ , Φ , Q ⟩ id) id (completed v) ⟫

  -- S-RESOLVE: Dependent → Completed when all deps ready
  S-RESOLVE : ∀ {e ρ Φ Q id deps combine vs} →
    lookup-future Φ id ≡ just (dependent deps combine) →
    collect-values Φ deps ≡ just vs →
    all-completed Φ deps ≡ true →  
    ⟪ e , ⟨ ρ , Φ , Q ⟩ ⟫ ⟶
    ⟪ e , update-future ⟨ ρ , Φ , Q ⟩ id (completed (combine vs)) ⟫