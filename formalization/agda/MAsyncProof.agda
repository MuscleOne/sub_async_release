-- Standalone test for M-ASYNC-preserves proof
-- Will be integrated into WFPreservation.agda once it compiles

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)  
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; _≢_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Nat using (ℕ; zero; suc; _≟_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (<-irrefl; n<1+n; m<n⇒m<1+n; <⇒≢)

open import SubAsync
open import WellFormedness

module MAsyncProof where

-- ============================================================================
-- HELPER LEMMAS
-- ============================================================================

-- Lookup after prepend returns the new value (same key)
lookup-update-same : ∀ (Φ : FutureTable) (id : Id) (σ : Status) →
  lookup-future ((id , σ) ∷ Φ) id ≡ just σ
lookup-update-same Φ id σ with id ≟ id
... | yes refl = refl
... | no id≢id = ⊥-elim (id≢id refl)

-- Lookup with a different key falls through to the tail
lookup-prepend-neq : ∀ (Φ : FutureTable) (id id' : Id) (σ : Status) →
  id ≢ id' → lookup-future ((id' , σ) ∷ Φ) id ≡ lookup-future Φ id
lookup-prepend-neq Φ id id' σ neq with id ≟ id'
... | yes id≡id' = ⊥-elim (neq id≡id')
... | no  _      = refl

-- Domain membership lifts through prepend
id-in-domain-prepend : ∀ (Φ : FutureTable) (id id' : Id) (σ' : Status) →
  id-in-domain id Φ → id-in-domain id ((id' , σ') ∷ Φ)
id-in-domain-prepend Φ id id' σ' (σ , lk-eq) with id ≟ id'
... | yes _ = σ' , refl
... | no  _ = σ , lk-eq

-- Map over All
all-map : ∀ {A : Set} {P Q : A → Set} {xs : List A} →
  (∀ {x} → P x → Q x) → All P xs → All Q xs
all-map f All.[] = All.[]
all-map f (px All.∷ pxs) = f px All.∷ all-map f pxs

-- fresh-id is not in domain of Φ
fresh-id-not-in-domain : (Φ : FutureTable) →
  (∀ id σ → lookup-future Φ id ≡ just σ → id < fresh-id Φ) →
  ¬ (id-in-domain (fresh-id Φ) Φ)
fresh-id-not-in-domain Φ all-below (σ , lookup-eq) = <-irrefl refl (all-below (fresh-id Φ) σ lookup-eq)

-- ============================================================================
-- M-ASYNC PRESERVES WF
-- ============================================================================

M-ASYNC-preserves : ∀ {ρ Φ Q e} →
  WF ⟨ ρ , Φ , Q ⟩ →
  WF ⟨ ρ , (fresh-id Φ , pending e ρ) ∷ Φ , fresh-id Φ ∷ Q ⟩
M-ASYNC-preserves {ρ} {Φ} {Q} {e} (wf-invariant cond1 cond2 cond3 cond4 cond5 cond6) =
  wf-invariant cond1' cond2' cond3' cond4' cond5' cond6'
  where
    fid = fresh-id Φ
    Φ' = (fid , pending e ρ) ∷ Φ
    Q' = fid ∷ Q

    -- Core helpers used across conditions
    -- Convert lookup in Φ' to lookup in Φ when id ≢ fid
    lk-to-orig : ∀ {id σ} → id ≢ fid →
      lookup-future Φ' id ≡ just σ → lookup-future Φ id ≡ just σ
    lk-to-orig {id} neq lk = trans (sym (lookup-prepend-neq Φ id fid (pending e ρ) neq)) lk

    -- Identify σ when looking up at fid: must be the pending we added
    lk-at-fid : ∀ {σ} → lookup-future Φ' fid ≡ just σ → σ ≡ pending e ρ
    lk-at-fid lk with trans (sym (lookup-update-same Φ fid (pending e ρ))) lk
    ... | refl = refl

    -----------------------------------------------------------------------
    -- Condition 1: Q' tracks exactly the pending Futures in Φ'
    -----------------------------------------------------------------------
    cond1' : ∀ id → (id ∈ Q') ↔
             (∃[ e' ] ∃[ ρ' ] (lookup-future Φ' id ≡ just (pending e' ρ')))
    cond1' id = fwd , bwd
      where
        fwd : id ∈ Q' → ∃[ e' ] ∃[ ρ' ] (lookup-future Φ' id ≡ just (pending e' ρ'))
        fwd (here refl) = e , ρ , lookup-update-same Φ fid (pending e ρ)
        fwd (there mem) = e₀ , ρ₀ , lk'
          where
            old  = proj₁ (cond1 id) mem
            e₀   = proj₁ old
            ρ₀   = proj₁ (proj₂ old)
            lk₀  = proj₂ (proj₂ old)
            id≢fid : id ≢ fid
            id≢fid = <⇒≢ (cond5 id (pending e₀ ρ₀) lk₀)
            lk' : lookup-future Φ' id ≡ just (pending e₀ ρ₀)
            lk' = trans (lookup-prepend-neq Φ id fid (pending e ρ) id≢fid) lk₀

        bwd : (∃[ e' ] ∃[ ρ' ] (lookup-future Φ' id ≡ just (pending e' ρ'))) → id ∈ Q'
        bwd (e' , ρ' , lk) = go (id ≟ fid)
          where
            go : Dec (id ≡ fid) → id ∈ Q'
            go (yes refl) = here refl
            go (no neq)   = there (proj₂ (cond1 id) (e' , ρ' , lk-to-orig neq lk))

    -----------------------------------------------------------------------
    -- Condition 2: No dangling dependencies
    -----------------------------------------------------------------------
    cond2' : ∀ id σ → lookup-future Φ' id ≡ just σ →
              All (λ id' → id-in-domain id' Φ') (get-deps σ)
    cond2' id σ lk = go (id ≟ fid)
      where
        go : Dec (id ≡ fid) → All (λ id' → id-in-domain id' Φ') (get-deps σ)
        go (yes refl) with lk-at-fid lk
        ... | refl = All.[]   -- get-deps (pending e ρ) = []
        go (no neq) =
          all-map (id-in-domain-prepend Φ _ fid (pending e ρ))
                  (cond2 id σ (lk-to-orig neq lk))

    -----------------------------------------------------------------------
    -- Condition 3: No self-cycles, no duplicates
    -----------------------------------------------------------------------
    cond3' : ∀ id deps f → lookup-future Φ' id ≡ just (dependent deps f) →
                   no-self-ref id deps × NoDup deps
    cond3' id deps f lk = go (id ≟ fid)
      where
        go : Dec (id ≡ fid) → no-self-ref id deps × NoDup deps
        go (yes refl) with lk-at-fid lk
        ... | ()   -- pending ≢ dependent
        go (no neq) = cond3 id deps f (lk-to-orig neq lk)

    -----------------------------------------------------------------------
    -- Condition 4: No dangling Future refs in environment
    -----------------------------------------------------------------------
    cond4' : ∀ x id → lookup ρ x ≡ just (futureV id) →
              id-in-domain id Φ'
    cond4' x id lk = id-in-domain-prepend Φ id fid (pending e ρ) (cond4 x id lk)

    -----------------------------------------------------------------------
    -- Condition 5: All ids < fresh-id (sequential allocation)
    -- fresh-id Φ' = suc fid
    -----------------------------------------------------------------------
    cond5' : ∀ id σ → lookup-future Φ' id ≡ just σ → id < fresh-id Φ'
    cond5' id σ lk = go (id ≟ fid)
      where
        go : Dec (id ≡ fid) → id < fresh-id Φ'
        go (yes refl) = n<1+n fid
        go (no neq)   = m<n⇒m<1+n (cond5 id σ (lk-to-orig neq lk))

    -----------------------------------------------------------------------
    -- Condition 6: NoDup (fid ∷ Q)
    -----------------------------------------------------------------------
    fid-not-in-Q : ¬ (fid ∈ Q)
    fid-not-in-Q mem =
      let (_ , _ , lk) = proj₁ (cond1 fid) mem in
      fresh-id-not-in-domain Φ cond5 (pending _ _ , lk)

    cond6' : NoDup (fid ∷ Q)
    cond6' = fid-not-in-Q , cond6
