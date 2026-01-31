-- Well-Formedness invariant for Sub_Async
-- Corresponds to WF(s) from SLIDES_CORE_RULES.md

open import Data.List using (List; []; _∷_; _++_; any; all; filter)  
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import SubAsync

module WellFormedness where

-- Helper: biconditional
_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

-- Helper: check if id is in queue
_∈Q_ : Id → PendingQueue → Set
id ∈Q Q = id ∈ Q

-- Helper: check if id is in domain of future table
id-in-domain : Id → FutureTable → Set  
id-in-domain id Φ = ∃[ σ ] (lookup-future Φ id ≡ just σ)

-- Helper: extract dependency list from Dependent status
get-deps : Status → List Id
get-deps (pending _ _) = []
get-deps (completed _) = []  
get-deps (dependent deps _) = deps

-- Helper: no duplicates in list
NoDup : {A : Set} → List A → Set
NoDup [] = ⊤  
NoDup (x ∷ xs) = (¬ (x ∈ xs)) × NoDup xs
  where open import Data.Unit using (⊤)

-- Helper: no self-reference in dependency list
no-self-ref : Id → List Id → Set  
no-self-ref id deps = ¬ (id ∈ deps)

-- WELL-FORMEDNESS INVARIANT
-- Corresponds to WF(s) from slides
data WF (s : State) : Set where
  wf-invariant : 
    -- 1. Q tracks exactly the pending Futures
    (∀ id → (id ∈Q (get-queue s)) ↔ 
             (∃[ e ] ∃[ ρ ] (lookup-future (get-futures s) id ≡ just (pending e ρ)))) →
    
    -- 2. No dangling dependencies  
    (∀ id σ → lookup-future (get-futures s) id ≡ just σ →
              All (λ id' → id-in-domain id' (get-futures s)) (get-deps σ)) →
    
    -- 3. No self-cycles and no duplicates in dependency lists
    (∀ id deps f → lookup-future (get-futures s) id ≡ just (dependent deps f) →
                   no-self-ref id deps × NoDup deps) →
    
    -- 4. No dangling Future references in environment
    (∀ x id → lookup (get-env s) x ≡ just (futureV id) →
              id-in-domain id (get-futures s)) →
    
    WF s

-- Helper: biconditional (moved after definition)
-- _↔_ : Set → Set → Set  
-- A ↔ B = (A → B) × (B → A)

-- Fresh id generation: returns length of FutureTable
-- This guarantees the returned id is not already used
-- (assuming ids are allocated sequentially: 0, 1, 2, ...)
fresh-id : FutureTable → Id  
fresh-id [] = zero
fresh-id (_ ∷ rest) = suc (fresh-id rest)

-- State update operations (from slides)
-- s[id ↦ σ] - update future table  
update-future : State → Id → Status → State
update-future ⟨ ρ , Φ , Q ⟩ id σ = ⟨ ρ , (id , σ) ∷ Φ , Q ⟩

-- s ⊕ id - add to queue
add-to-queue : State → Id → State  
add-to-queue ⟨ ρ , Φ , Q ⟩ id = ⟨ ρ , Φ , id ∷ Q ⟩

-- s ⊖ id - remove from queue
remove-from-queue : State → Id → State
remove-from-queue ⟨ ρ , Φ , Q ⟩ id = ⟨ ρ , Φ , filter-out id Q ⟩
  where
  filter-out : Id → List Id → List Id
  filter-out _ [] = []
  filter-out target (x ∷ xs) with target ≟ x  
  ... | yes _ = filter-out target xs
  ... | no  _ = x ∷ filter-out target xs