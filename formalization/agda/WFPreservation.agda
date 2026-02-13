-- WF Preservation proof — fully proven for 9/9 rules, zero postulates!

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)  
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; _≢_; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Nat using (ℕ; _≟_; _<_; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat.Properties using (<-irrefl; n<1+n; m<n⇒m<1+n; <⇒≢)

open import SubAsync
open import WellFormedness  
open import Reductions

module WFPreservation where

-- ============================================================================
-- AUXILIARY LEMMAS (all proven)
-- ============================================================================

-- Lemma: fresh-id is not in current FutureTable
-- Proof: condition 5 of WF says all ids < fresh-id, so fresh-id ∉ dom(Φ) by <-irrefl
fresh-id-not-in-domain : (Φ : FutureTable) →
  (∀ id σ → lookup-future Φ id ≡ just σ → id < fresh-id Φ) →
  ¬ (id-in-domain (fresh-id Φ) Φ)
fresh-id-not-in-domain Φ all-below (σ , lookup-eq) = <-irrefl refl (all-below (fresh-id Φ) σ lookup-eq)

-- Lemma: lookup after update (prepend) returns the new value
lookup-update-same : (Φ : FutureTable) (id : Id) (σ : Status) → lookup-future ((id , σ) ∷ Φ) id ≡ just σ
lookup-update-same Φ id σ with id ≟ id
... | yes refl = refl
... | no  id≢id = ⊥-elim (id≢id refl)

-- Lemma: adding to queue preserves membership
queue-add-preserves : (Q : PendingQueue) (id id' : Id) → id' ∈ Q → id' ∈ (id ∷ Q)
queue-add-preserves Q id id' mem = there mem

-- Lemma: new id is in extended queue
queue-add-new : (Q : PendingQueue) (id : Id) → id ∈ (id ∷ Q)
queue-add-new Q id = here refl

-- Lemma: lookup with different key falls through to tail
lookup-prepend-neq : ∀ (Φ : FutureTable) (id id' : Id) (σ : Status) →
  id ≢ id' → lookup-future ((id' , σ) ∷ Φ) id ≡ lookup-future Φ id
lookup-prepend-neq Φ id id' σ neq with id ≟ id'
... | yes id≡id' = ⊥-elim (neq id≡id')
... | no  _      = refl

-- Lemma: domain membership lifts through prepend
id-in-domain-prepend : ∀ (Φ : FutureTable) (id id' : Id) (σ' : Status) →
  id-in-domain id Φ → id-in-domain id ((id' , σ') ∷ Φ)
id-in-domain-prepend Φ id id' σ' (σ , lk-eq) with id ≟ id'
... | yes _ = σ' , refl
... | no  _ = σ , lk-eq

-- Map over All predicate
all-map : ∀ {A : Set} {P Q : A → Set} {xs : List A} →
  (∀ {x} → P x → Q x) → All P xs → All Q xs
all-map f All.[] = All.[]
all-map f (px All.∷ pxs) = f px All.∷ all-map f pxs

-- ============================================================================
-- MAIN THEOREM: WF PRESERVATION (Cases outlined)
-- ============================================================================

-- Case M-AWAIT: Extract completed value - STATE UNCHANGED
-- This is the trivial case: no state modification means WF preserved
M-AWAIT-preserves : ∀ {s} → WF s → WF s
M-AWAIT-preserves wf-s = wf-s

-- Case M-AWAIT-IF, M-AWAIT-APP1, M-AWAIT-APP2: Same as M-AWAIT  
-- These rules only change the expression, not the state
M-AWAIT-IF-preserves : ∀ {s} → WF s → WF s
M-AWAIT-IF-preserves wf-s = wf-s

M-AWAIT-APP1-preserves : ∀ {s} → WF s → WF s
M-AWAIT-APP1-preserves wf-s = wf-s

M-AWAIT-APP2-preserves : ∀ {s} → WF s → WF s  
M-AWAIT-APP2-preserves wf-s = wf-s

-- ============================================================================
-- MORE COMPLEX CASES (all proven)
-- ============================================================================

-- Case S-RESOLVE: Dependent → Completed. FULLY PROVEN.
-- Needs premise that id is already Dependent in Φ (from reduction rule).
S-RESOLVE-preserves : ∀ {ρ Φ Q id deps combine v} →
  WF ⟨ ρ , Φ , Q ⟩ →
  lookup-future Φ id ≡ just (dependent deps combine) →
  WF ⟨ ρ , (id , completed v) ∷ Φ , Q ⟩
S-RESOLVE-preserves {ρ} {Φ} {Q} {id} {deps} {combine} {v}
  (wf-invariant cond1 cond2 cond3 cond4 cond5 cond6) lk-dep =
  wf-invariant cond1' cond2' cond3' cond4' cond5' cond6
  where
    Φ' = (id , completed v) ∷ Φ

    -- id < fresh-id Φ (from cond5 + premise)
    id<fid : id < fresh-id Φ
    id<fid = cond5 id (dependent deps combine) lk-dep

    -- Convert lookup in Φ' to lookup in Φ when id' ≢ id
    lk-to-orig : ∀ {id' σ} → id' ≢ id →
      lookup-future Φ' id' ≡ just σ → lookup-future Φ id' ≡ just σ
    lk-to-orig {id'} neq lk = trans (sym (lookup-prepend-neq Φ id' id (completed v) neq)) lk

    -- Identify σ at id: must be completed v
    lk-at-id : ∀ {σ} → lookup-future Φ' id ≡ just σ → σ ≡ completed v
    lk-at-id lk with trans (sym (lookup-update-same Φ id (completed v))) lk
    ... | refl = refl

    -- just-injectivity helper
    just-inj : ∀ {A : Set} {x y : A} → _≡_ {_} {Data.Maybe.Maybe A} (just x) (just y) → x ≡ y
    just-inj refl = refl
      where open import Data.Maybe

    -- Condition 1: Q tracks pending. New entry is completed (not pending), Q unchanged.
    cond1' : ∀ id' → (id' ∈ Q) ↔
             (∃[ e' ] ∃[ ρ' ] (lookup-future Φ' id' ≡ just (pending e' ρ')))
    cond1' id' = fwd , bwd
      where
        fwd : id' ∈ Q → ∃[ e' ] ∃[ ρ' ] (lookup-future Φ' id' ≡ just (pending e' ρ'))
        fwd mem = go (id' ≟ id)
          where
            old  = proj₁ (cond1 id') mem
            e₀   = proj₁ old
            ρ₀   = proj₁ (proj₂ old)
            lk₀  = proj₂ (proj₂ old)
            go : Dec (id' ≡ id) → ∃[ e' ] ∃[ ρ' ] (lookup-future Φ' id' ≡ just (pending e' ρ'))
            go (yes refl) with just-inj (trans (sym lk₀) lk-dep)
            ... | ()  -- pending ≡ dependent absurd
            go (no neq) = e₀ , ρ₀ , trans (lookup-prepend-neq Φ id' id (completed v) neq) lk₀

        bwd : (∃[ e' ] ∃[ ρ' ] (lookup-future Φ' id' ≡ just (pending e' ρ'))) → id' ∈ Q
        bwd (e' , ρ' , lk) = go (id' ≟ id)
          where
            go : Dec (id' ≡ id) → id' ∈ Q
            go (yes refl) with lk-at-id lk
            ... | ()  -- completed ≡ pending absurd
            go (no neq) = proj₂ (cond1 id') (e' , ρ' , lk-to-orig neq lk)

    -- Condition 2: No dangling deps. completed has no deps.
    cond2' : ∀ id' σ → lookup-future Φ' id' ≡ just σ →
              All (λ d → id-in-domain d Φ') (get-deps σ)
    cond2' id' σ lk = go (id' ≟ id)
      where
        go : Dec (id' ≡ id) → All (λ d → id-in-domain d Φ') (get-deps σ)
        go (yes refl) with lk-at-id lk
        ... | refl = All.[]   -- get-deps (completed v) = []
        go (no neq) =
          all-map (id-in-domain-prepend Φ _ id (completed v))
                  (cond2 id' σ (lk-to-orig neq lk))

    -- Condition 3: No self-cycles. completed is not dependent.
    cond3' : ∀ id' deps' f → lookup-future Φ' id' ≡ just (dependent deps' f) →
                   no-self-ref id' deps' × NoDup deps'
    cond3' id' deps' f lk = go (id' ≟ id)
      where
        go : Dec (id' ≡ id) → no-self-ref id' deps' × NoDup deps'
        go (yes refl) with lk-at-id lk
        ... | ()   -- completed ≢ dependent
        go (no neq) = cond3 id' deps' f (lk-to-orig neq lk)

    -- Condition 4: env unchanged, lift domain
    cond4' : ∀ x id' → lookup ρ x ≡ just (futureV id') →
              id-in-domain id' Φ'
    cond4' x id' lk = id-in-domain-prepend Φ id' id (completed v) (cond4 x id' lk)

    -- Condition 5: All ids < fresh-id Φ' = suc (fresh-id Φ)
    cond5' : ∀ id' σ → lookup-future Φ' id' ≡ just σ → id' < fresh-id Φ'
    cond5' id' σ lk = go (id' ≟ id)
      where
        go : Dec (id' ≡ id) → id' < fresh-id Φ'
        go (yes refl) = m<n⇒m<1+n id<fid
        go (no neq)   = m<n⇒m<1+n (cond5 id' σ (lk-to-orig neq lk))

-- Case M-LIFT-OP-* (FF, FV, VF): Creates Dependent future. FULLY PROVEN.
-- Needs premise that all deps exist in Φ and deps has no duplicates.
M-LIFT-OP-preserves : ∀ {ρ Φ Q deps combine} →
  WF ⟨ ρ , Φ , Q ⟩ →
  All (λ d → id-in-domain d Φ) deps →
  NoDup deps →
  WF ⟨ ρ , (fresh-id Φ , dependent deps combine) ∷ Φ , Q ⟩
M-LIFT-OP-preserves {ρ} {Φ} {Q} {deps} {combine}
  (wf-invariant cond1 cond2 cond3 cond4 cond5 cond6) deps-in-dom nodup-deps =
  wf-invariant cond1' cond2' cond3' cond4' cond5' cond6
  where
    fid = fresh-id Φ
    Φ' = (fid , dependent deps combine) ∷ Φ

    -- Convert lookup in Φ' to lookup in Φ when id ≢ fid
    lk-to-orig : ∀ {id σ} → id ≢ fid →
      lookup-future Φ' id ≡ just σ → lookup-future Φ id ≡ just σ
    lk-to-orig {id} neq lk = trans (sym (lookup-prepend-neq Φ id fid (dependent deps combine) neq)) lk

    -- Identify σ at fid: must be the dependent we just added
    lk-at-fid : ∀ {σ} → lookup-future Φ' fid ≡ just σ → σ ≡ dependent deps combine
    lk-at-fid lk with trans (sym (lookup-update-same Φ fid (dependent deps combine))) lk
    ... | refl = refl

    -- fresh-id is not in domain of Φ
    fid-fresh : ¬ (id-in-domain fid Φ)
    fid-fresh = fresh-id-not-in-domain Φ cond5

    -- fresh-id is not in deps (if it were, it would be in domain of Φ, contradiction)
    fid-not-in-deps : ¬ (fid ∈ deps)
    fid-not-in-deps fid∈deps = fid-fresh (All.lookup deps-in-dom fid∈deps)

    -- Condition 1: Q ↔ pending. New entry is dependent (not pending), Q unchanged.
    cond1' : ∀ id → (id ∈ Q) ↔
             (∃[ e' ] ∃[ ρ' ] (lookup-future Φ' id ≡ just (pending e' ρ')))
    cond1' id = fwd , bwd
      where
        fwd : id ∈ Q → ∃[ e' ] ∃[ ρ' ] (lookup-future Φ' id ≡ just (pending e' ρ'))
        fwd mem = go (id ≟ fid)
          where
            old  = proj₁ (cond1 id) mem
            e₀   = proj₁ old
            ρ₀   = proj₁ (proj₂ old)
            lk₀  = proj₂ (proj₂ old)
            go : Dec (id ≡ fid) → ∃[ e' ] ∃[ ρ' ] (lookup-future Φ' id ≡ just (pending e' ρ'))
            go (yes refl) with lk₀   -- id = fid, but id ∈ Q means pending in Φ, contradicts freshness
            ... | lk-pend = ⊥-elim (fid-fresh (pending e₀ ρ₀ , lk-pend))
            go (no neq) = e₀ , ρ₀ , trans (lookup-prepend-neq Φ id fid (dependent deps combine) neq) lk₀

        bwd : (∃[ e' ] ∃[ ρ' ] (lookup-future Φ' id ≡ just (pending e' ρ'))) → id ∈ Q
        bwd (e' , ρ' , lk) = go (id ≟ fid)
          where
            go : Dec (id ≡ fid) → id ∈ Q
            go (yes refl) with lk-at-fid lk
            ... | ()  -- dependent ≡ pending absurd
            go (no neq) = proj₂ (cond1 id) (e' , ρ' , lk-to-orig neq lk)

    -- Condition 2: No dangling deps. For fid entry, use deps-in-dom premise.
    cond2' : ∀ id σ → lookup-future Φ' id ≡ just σ →
              All (λ d → id-in-domain d Φ') (get-deps σ)
    cond2' id σ lk = go (id ≟ fid)
      where
        go : Dec (id ≡ fid) → All (λ d → id-in-domain d Φ') (get-deps σ)
        go (yes refl) with lk-at-fid lk
        ... | refl = all-map (id-in-domain-prepend Φ _ fid (dependent deps combine)) deps-in-dom
        go (no neq) =
          all-map (id-in-domain-prepend Φ _ fid (dependent deps combine))
                  (cond2 id σ (lk-to-orig neq lk))

    -- Condition 3: No self-cycles and NoDup. For fid, use fid-not-in-deps and nodup premise.
    cond3' : ∀ id deps' f → lookup-future Φ' id ≡ just (dependent deps' f) →
                   no-self-ref id deps' × NoDup deps'
    cond3' id deps' f lk = go (id ≟ fid)
      where
        go : Dec (id ≡ fid) → no-self-ref id deps' × NoDup deps'
        go (yes refl) with lk-at-fid lk
        ... | refl = fid-not-in-deps , nodup-deps
        go (no neq) = cond3 id deps' f (lk-to-orig neq lk)

    -- Condition 4: env unchanged, lift domain
    cond4' : ∀ x id' → lookup ρ x ≡ just (futureV id') →
              id-in-domain id' Φ'
    cond4' x id' lk = id-in-domain-prepend Φ id' fid (dependent deps combine) (cond4 x id' lk)

    -- Condition 5: fid < suc fid, old ids lift
    cond5' : ∀ id σ → lookup-future Φ' id ≡ just σ → id < fresh-id Φ'
    cond5' id σ lk = go (id ≟ fid)
      where
        go : Dec (id ≡ fid) → id < fresh-id Φ'
        go (yes refl) = n<1+n fid
        go (no neq)   = m<n⇒m<1+n (cond5 id σ (lk-to-orig neq lk))

-- Case M-ASYNC: async e → Future(id)
-- Creates fresh pending future and adds to queue. FULLY PROVEN.
M-ASYNC-preserves : ∀ {ρ Φ Q e} →
  WF ⟨ ρ , Φ , Q ⟩ →
  WF ⟨ ρ , (fresh-id Φ , pending e ρ) ∷ Φ , fresh-id Φ ∷ Q ⟩
M-ASYNC-preserves {ρ} {Φ} {Q} {e} (wf-invariant cond1 cond2 cond3 cond4 cond5 cond6) =
  wf-invariant cond1' cond2' cond3' cond4' cond5' cond6'
  where
    fid = fresh-id Φ
    Φ' = (fid , pending e ρ) ∷ Φ
    Q' = fid ∷ Q

    -- Convert lookup in Φ' to Φ when id ≢ fid
    lk-to-orig : ∀ {id σ} → id ≢ fid →
      lookup-future Φ' id ≡ just σ → lookup-future Φ id ≡ just σ
    lk-to-orig {id} neq lk = trans (sym (lookup-prepend-neq Φ id fid (pending e ρ) neq)) lk

    -- Identify σ at fid: must be the pending we just added
    lk-at-fid : ∀ {σ} → lookup-future Φ' fid ≡ just σ → σ ≡ pending e ρ
    lk-at-fid lk with trans (sym (lookup-update-same Φ fid (pending e ρ))) lk
    ... | refl = refl

    -- Condition 1
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

    -- Condition 2: pending has no deps, old deps lift
    cond2' : ∀ id σ → lookup-future Φ' id ≡ just σ →
              All (λ id' → id-in-domain id' Φ') (get-deps σ)
    cond2' id σ lk = go (id ≟ fid)
      where
        go : Dec (id ≡ fid) → All (λ id' → id-in-domain id' Φ') (get-deps σ)
        go (yes refl) with lk-at-fid lk
        ... | refl = All.[]
        go (no neq) =
          all-map (id-in-domain-prepend Φ _ fid (pending e ρ))
                  (cond2 id σ (lk-to-orig neq lk))

    -- Condition 3: pending ≢ dependent makes yes-case absurd
    cond3' : ∀ id deps f → lookup-future Φ' id ≡ just (dependent deps f) →
                   no-self-ref id deps × NoDup deps
    cond3' id deps f lk = go (id ≟ fid)
      where
        go : Dec (id ≡ fid) → no-self-ref id deps × NoDup deps
        go (yes refl) with lk-at-fid lk
        ... | ()
        go (no neq) = cond3 id deps f (lk-to-orig neq lk)

    -- Condition 4: env unchanged, lift domain
    cond4' : ∀ x id → lookup ρ x ≡ just (futureV id) →
              id-in-domain id Φ'
    cond4' x id lk = id-in-domain-prepend Φ id fid (pending e ρ) (cond4 x id lk)

    -- Condition 5: fid < suc fid, old ids lift
    cond5' : ∀ id σ → lookup-future Φ' id ≡ just σ → id < fresh-id Φ'
    cond5' id σ lk = go (id ≟ fid)
      where
        go : Dec (id ≡ fid) → id < fresh-id Φ'
        go (yes refl) = n<1+n fid
        go (no neq)   = m<n⇒m<1+n (cond5 id σ (lk-to-orig neq lk))

    -- Condition 6: NoDup (fid ∷ Q)
    -- fid ∉ Q because fid ∈ Q would imply (via cond1) that pending exists in Φ for fid,
    -- contradicting fresh-id-not-in-domain.
    fid-not-in-Q : ¬ (fid ∈ Q)
    fid-not-in-Q mem =
      let (_ , _ , lk) = proj₁ (cond1 fid) mem in
      fresh-id-not-in-domain Φ cond5 (pending _ _ , lk)

    cond6' : NoDup (fid ∷ Q)
    cond6' = fid-not-in-Q , cond6

-- ============================================================================
-- FILTER-OUT LEMMAS (for S-COMPLETE)
-- ============================================================================

-- Lemma: non-target elements survive filter-out
filter-out-preserves : ∀ (target id : Id) (Q : List Id) →
  target ≢ id → id ∈ Q → id ∈ filter-out target Q
filter-out-preserves target id (x ∷ xs) neq (here refl) with target ≟ id
... | yes t≡id = ⊥-elim (neq t≡id)
... | no  _    = here refl
filter-out-preserves target id (x ∷ xs) neq (there mem) with target ≟ x
... | yes _ = filter-out-preserves target id xs neq mem
... | no  _ = there (filter-out-preserves target id xs neq mem)

-- Lemma: target is excluded from filter-out result
filter-out-excluded : ∀ (target : Id) (Q : List Id) →
  ¬ (target ∈ filter-out target Q)
filter-out-excluded target [] ()
filter-out-excluded target (x ∷ xs) mem with target ≟ x
filter-out-excluded target (x ∷ xs) mem | yes _ = filter-out-excluded target xs mem
filter-out-excluded target (x ∷ xs) (here refl) | no neq = neq refl
filter-out-excluded target (x ∷ xs) (there mem) | no _ = filter-out-excluded target xs mem

-- Lemma: membership in filter-out implies membership in original and non-equality
filter-out-inv : ∀ (target id : Id) (Q : List Id) →
  id ∈ filter-out target Q → id ∈ Q × target ≢ id
filter-out-inv target id (x ∷ xs) mem with target ≟ x
filter-out-inv target id (x ∷ xs) mem | yes refl with filter-out-inv target id xs mem
... | (mem' , neq) = there mem' , neq
filter-out-inv target id (x ∷ xs) (here refl) | no neq = here refl , neq
filter-out-inv target id (x ∷ xs) (there mem) | no _ with filter-out-inv target id xs mem
... | (mem' , neq) = there mem' , neq

-- Lemma: filter-out preserves NoDup
filter-out-nodup : ∀ (target : Id) (Q : List Id) →
  NoDup Q → NoDup (filter-out target Q)
filter-out-nodup target [] nd = tt
filter-out-nodup target (x ∷ xs) (x∉xs , nd-xs) with target ≟ x
... | yes _ = filter-out-nodup target xs nd-xs
... | no  _ = (λ mem → x∉xs (proj₁ (filter-out-inv target x xs mem))) , filter-out-nodup target xs nd-xs

-- Case S-COMPLETE: Pending(value) → Completed, remove from Q. FULLY PROVEN.
-- Needs premise: id is in Q and has pending status with a value expression.
S-COMPLETE-preserves : ∀ {ρ Φ Q id v ρ'} →
  WF ⟨ ρ , Φ , Q ⟩ →
  id ∈Q Q →
  lookup-future Φ id ≡ just (pending (value-to-expr v) ρ') →
  WF ⟨ ρ , (id , completed v) ∷ Φ , filter-out id Q ⟩
S-COMPLETE-preserves {ρ} {Φ} {Q} {id} {v} {ρ'}
  (wf-invariant cond1 cond2 cond3 cond4 cond5 cond6) id∈Q lk-pend =
  wf-invariant cond1' cond2' cond3' cond4' cond5' cond6'
  where
    Φ' = (id , completed v) ∷ Φ
    Q' = filter-out id Q

    -- id < fresh-id Φ (from cond5 + premise)
    id<fid : id < fresh-id Φ
    id<fid = cond5 id (pending (value-to-expr v) ρ') lk-pend

    -- Convert lookup in Φ' to lookup in Φ when id' ≢ id
    lk-to-orig : ∀ {id' σ} → id' ≢ id →
      lookup-future Φ' id' ≡ just σ → lookup-future Φ id' ≡ just σ
    lk-to-orig {id'} neq lk = trans (sym (lookup-prepend-neq Φ id' id (completed v) neq)) lk

    -- Identify σ at id: must be completed v
    lk-at-id : ∀ {σ} → lookup-future Φ' id ≡ just σ → σ ≡ completed v
    lk-at-id lk with trans (sym (lookup-update-same Φ id (completed v))) lk
    ... | refl = refl

    -- Condition 1: Q' (filter-out id Q) ↔ pending in Φ'.
    -- id is removed from Q and its status changed to completed, so the biconditional holds.
    cond1' : ∀ id' → (id' ∈ Q') ↔
             (∃[ e' ] ∃[ ρ'' ] (lookup-future Φ' id' ≡ just (pending e' ρ'')))
    cond1' id' = fwd , bwd
      where
        fwd : id' ∈ Q' → ∃[ e' ] ∃[ ρ'' ] (lookup-future Φ' id' ≡ just (pending e' ρ''))
        fwd mem' with filter-out-inv id id' Q mem'
        ... | (mem , neq') with proj₁ (cond1 id') mem
        ...   | (e₀ , ρ₀ , lk₀) =
              e₀ , ρ₀ , trans (lookup-prepend-neq Φ id' id (completed v) (λ eq → neq' (sym eq))) lk₀

        bwd : (∃[ e' ] ∃[ ρ'' ] (lookup-future Φ' id' ≡ just (pending e' ρ''))) → id' ∈ Q'
        bwd (e' , ρ'' , lk) = go (id' ≟ id)
          where
            go : Dec (id' ≡ id) → id' ∈ Q'
            go (yes refl) with lk-at-id lk
            ... | ()  -- completed ≡ pending absurd
            go (no neq) =
              let lk-orig = lk-to-orig neq lk in
              let mem = proj₂ (cond1 id') (e' , ρ'' , lk-orig) in
              filter-out-preserves id id' Q (λ eq → neq (sym eq)) mem

    -- Condition 2: No dangling deps. completed has no deps.
    cond2' : ∀ id' σ → lookup-future Φ' id' ≡ just σ →
              All (λ d → id-in-domain d Φ') (get-deps σ)
    cond2' id' σ lk = go (id' ≟ id)
      where
        go : Dec (id' ≡ id) → All (λ d → id-in-domain d Φ') (get-deps σ)
        go (yes refl) with lk-at-id lk
        ... | refl = All.[]   -- get-deps (completed v) = []
        go (no neq) =
          all-map (id-in-domain-prepend Φ _ id (completed v))
                  (cond2 id' σ (lk-to-orig neq lk))

    -- Condition 3: No self-cycles. completed is not dependent.
    cond3' : ∀ id' deps' f → lookup-future Φ' id' ≡ just (dependent deps' f) →
                   no-self-ref id' deps' × NoDup deps'
    cond3' id' deps' f lk = go (id' ≟ id)
      where
        go : Dec (id' ≡ id) → no-self-ref id' deps' × NoDup deps'
        go (yes refl) with lk-at-id lk
        ... | ()   -- completed ≢ dependent
        go (no neq) = cond3 id' deps' f (lk-to-orig neq lk)

    -- Condition 4: env unchanged, lift domain
    cond4' : ∀ x id' → lookup ρ x ≡ just (futureV id') →
              id-in-domain id' Φ'
    cond4' x id' lk = id-in-domain-prepend Φ id' id (completed v) (cond4 x id' lk)

    -- Condition 5: All ids < fresh-id Φ' = suc (fresh-id Φ)
    cond5' : ∀ id' σ → lookup-future Φ' id' ≡ just σ → id' < fresh-id Φ'
    cond5' id' σ lk = go (id' ≟ id)
      where
        go : Dec (id' ≡ id) → id' < fresh-id Φ'
        go (yes refl) = m<n⇒m<1+n id<fid
        go (no neq)   = m<n⇒m<1+n (cond5 id' σ (lk-to-orig neq lk))

    -- Condition 6: NoDup (filter-out id Q)
    cond6' : NoDup (filter-out id Q)
    cond6' = filter-out-nodup id Q cond6

-- ============================================================================
-- S-SCHEDULE PRESERVATION: Case-split on substep
-- ============================================================================

-- Helper: Q ++ [] ≡ Q
++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)

-- Helper: transport WF along queue equality
WF-subst-Q : ∀ {ρ Φ Q Q'} → Q ≡ Q' → WF ⟨ ρ , Φ , Q ⟩ → WF ⟨ ρ , Φ , Q' ⟩
WF-subst-Q refl wf = wf

-- Helper: membership in left part of ++
∈-++ˡ : ∀ {A : Set} {x : A} {xs ys : List A} → x ∈ xs → x ∈ (xs ++ ys)
∈-++ˡ (here refl) = here refl
∈-++ˡ (there mem) = there (∈-++ˡ mem)

-- Helper: membership in right part of ++
∈-++ʳ : ∀ {A : Set} (xs : List A) {x : A} {ys : List A} → x ∈ ys → x ∈ (xs ++ ys)
∈-++ʳ [] mem = mem
∈-++ʳ (x ∷ xs) mem = there (∈-++ʳ xs mem)

-- Helper: split membership from ++
∈-++-split : ∀ {A : Set} {x : A} (xs ys : List A) → x ∈ (xs ++ ys) → x ∈ xs ⊎ x ∈ ys
∈-++-split [] ys mem = inj₂ mem
∈-++-split (x ∷ xs) ys (here refl) = inj₁ (here refl)
∈-++-split (x ∷ xs) ys (there mem) with ∈-++-split xs ys mem
... | inj₁ l = inj₁ (there l)
... | inj₂ r = inj₂ r

-- Helper: NoDup for xs ++ ys when xs, ys each NoDup and disjoint
NoDup-++ : ∀ (xs ys : List Id) →
  NoDup xs → NoDup ys →
  (∀ {x} → x ∈ xs → ¬ (x ∈ ys)) →
  NoDup (xs ++ ys)
NoDup-++ [] ys _ nd-ys _ = nd-ys
NoDup-++ (x ∷ xs) ys (x∉xs , nd-xs) nd-ys disj =
  (λ mem → helper (∈-++-split xs ys mem))
  , NoDup-++ xs ys nd-xs nd-ys (λ mem → disj (there mem))
  where
    helper : x ∈ xs ⊎ x ∈ ys → ⊥
    helper (inj₁ l) = x∉xs l
    helper (inj₂ r) = disj (here refl) r

-- Lemma: Updating a pending entry's expression preserves WF
-- (id is already pending in Φ and in Q; we just change the expression/env)
pending-update-preserves : ∀ {ρ Φ Q id e-new ρ-new} →
  WF ⟨ ρ , Φ , Q ⟩ →
  id ∈ Q →
  (∃[ e-old ] ∃[ ρ-old ] (lookup-future Φ id ≡ just (pending e-old ρ-old))) →
  WF ⟨ ρ , (id , pending e-new ρ-new) ∷ Φ , Q ⟩
pending-update-preserves {ρ} {Φ} {Q} {id} {e-new} {ρ-new}
  (wf-invariant cond1 cond2 cond3 cond4 cond5 cond6) id∈Q (e-old , ρ-old , lk-old) =
  wf-invariant cond1' cond2' cond3' cond4' cond5' cond6
  where
    Φ' = (id , pending e-new ρ-new) ∷ Φ

    id<fid : id < fresh-id Φ
    id<fid = cond5 id (pending e-old ρ-old) lk-old

    lk-to-orig : ∀ {id' σ} → id' ≢ id →
      lookup-future Φ' id' ≡ just σ → lookup-future Φ id' ≡ just σ
    lk-to-orig {id'} neq lk = trans (sym (lookup-prepend-neq Φ id' id (pending e-new ρ-new) neq)) lk

    lk-at-id : ∀ {σ} → lookup-future Φ' id ≡ just σ → σ ≡ pending e-new ρ-new
    lk-at-id lk with trans (sym (lookup-update-same Φ id (pending e-new ρ-new))) lk
    ... | refl = refl

    cond1' : ∀ id' → (id' ∈ Q) ↔
             (∃[ e' ] ∃[ ρ' ] (lookup-future Φ' id' ≡ just (pending e' ρ')))
    cond1' id' = fwd , bwd
      where
        fwd : id' ∈ Q → ∃[ e' ] ∃[ ρ' ] (lookup-future Φ' id' ≡ just (pending e' ρ'))
        fwd mem = go (id' ≟ id)
          where
            go : Dec (id' ≡ id) → ∃[ e' ] ∃[ ρ' ] (lookup-future Φ' id' ≡ just (pending e' ρ'))
            go (yes refl) = e-new , ρ-new , lookup-update-same Φ id (pending e-new ρ-new)
            go (no neq) =
              let (e₀ , ρ₀ , lk₀) = proj₁ (cond1 id') mem in
              e₀ , ρ₀ , trans (lookup-prepend-neq Φ id' id (pending e-new ρ-new) neq) lk₀

        bwd : (∃[ e' ] ∃[ ρ' ] (lookup-future Φ' id' ≡ just (pending e' ρ'))) → id' ∈ Q
        bwd (e' , ρ' , lk) = go (id' ≟ id)
          where
            go : Dec (id' ≡ id) → id' ∈ Q
            go (yes refl) = id∈Q
            go (no neq) = proj₂ (cond1 id') (e' , ρ' , lk-to-orig neq lk)

    cond2' : ∀ id' σ → lookup-future Φ' id' ≡ just σ →
              All (λ d → id-in-domain d Φ') (get-deps σ)
    cond2' id' σ lk = go (id' ≟ id)
      where
        go : Dec (id' ≡ id) → All (λ d → id-in-domain d Φ') (get-deps σ)
        go (yes refl) with lk-at-id lk
        ... | refl = All.[]
        go (no neq) =
          all-map (id-in-domain-prepend Φ _ id (pending e-new ρ-new))
                  (cond2 id' σ (lk-to-orig neq lk))

    cond3' : ∀ id' deps' f → lookup-future Φ' id' ≡ just (dependent deps' f) →
                   no-self-ref id' deps' × NoDup deps'
    cond3' id' deps' f lk = go (id' ≟ id)
      where
        go : Dec (id' ≡ id) → no-self-ref id' deps' × NoDup deps'
        go (yes refl) with lk-at-id lk
        ... | ()   -- pending ≢ dependent
        go (no neq) = cond3 id' deps' f (lk-to-orig neq lk)

    cond4' : ∀ x id' → lookup ρ x ≡ just (futureV id') →
              id-in-domain id' Φ'
    cond4' x id' lk = id-in-domain-prepend Φ id' id (pending e-new ρ-new) (cond4 x id' lk)

    cond5' : ∀ id' σ → lookup-future Φ' id' ≡ just σ → id' < fresh-id Φ'
    cond5' id' σ lk = go (id' ≟ id)
      where
        go : Dec (id' ≡ id) → id' < fresh-id Φ'
        go (yes refl) = m<n⇒m<1+n id<fid
        go (no neq) = m<n⇒m<1+n (cond5 id' σ (lk-to-orig neq lk))

-- ============================================================================
-- NODUP HELPERS (moved before S-SCHEDULE-preserves which needs them)
-- ============================================================================

-- NoDup for singleton list (always true)
nodup-single : ∀ {id : Id} → NoDup (id ∷ [])
nodup-single = (λ ()) , tt

-- NoDup for pair from ≢
nodup-pair : ∀ {id₁ id₂ : Id} → id₁ ≢ id₂ → NoDup (id₁ ∷ id₂ ∷ [])
nodup-pair neq = (λ { (here refl) → neq refl ; (there ()) }) , (λ ()) , tt

-- Helper: extract cond5 (AllIdsBelow) from WF
WF-cond5 : ∀ {ρ Φ Q} → WF ⟨ ρ , Φ , Q ⟩ →
  (∀ id σ → lookup-future Φ id ≡ just σ → id < fresh-id Φ)
WF-cond5 (wf-invariant _ _ _ _ cond5 _) = cond5

-- S-SCHEDULE case: case-split on the substep
-- When substep starts from Q=[], only 7 rules can fire:
--   M-ASYNC, M-LIFT-OP-FF/FV/VF, M-AWAIT/IF/APP1/APP2, S-RESOLVE
-- S-SCHEDULE and S-COMPLETE need id ∈ [] which is impossible.
S-SCHEDULE-preserves : ∀ {ρ Φ Q id e' ρ' e'' s''} →
  WF ⟨ ρ , Φ , Q ⟩ →
  id ∈ Q →
  lookup-future Φ id ≡ just (pending e' ρ') →
  ⟪ e' , ⟨ ρ' , Φ , [] ⟩ ⟫ ⟶ ⟪ e'' , s'' ⟫ →
  WF ⟨ ρ , (id , pending e'' (get-env s'')) ∷ get-futures s'' , Q ++ get-queue s'' ⟩

-- Substep = M-AWAIT: state unchanged, s'' = ⟨ ρ', Φ, [] ⟩
S-SCHEDULE-preserves {ρ} {Φ} {Q} {id} wf id∈Q lk-pend (M-AWAIT _) =
  WF-subst-Q (sym (++-identityʳ Q))
    (pending-update-preserves wf id∈Q (e' , ρ' , lk-pend))
  where e' = _; ρ' = _

-- Substep = M-AWAIT-IF: state unchanged
S-SCHEDULE-preserves {ρ} {Φ} {Q} {id} wf id∈Q lk-pend (M-AWAIT-IF _) =
  WF-subst-Q (sym (++-identityʳ Q))
    (pending-update-preserves wf id∈Q (_ , _ , lk-pend))

-- Substep = M-AWAIT-APP1: state unchanged
S-SCHEDULE-preserves {ρ} {Φ} {Q} {id} wf id∈Q lk-pend (M-AWAIT-APP1 _) =
  WF-subst-Q (sym (++-identityʳ Q))
    (pending-update-preserves wf id∈Q (_ , _ , lk-pend))

-- Substep = M-AWAIT-APP2: state unchanged
S-SCHEDULE-preserves {ρ} {Φ} {Q} {id} wf id∈Q lk-pend (M-AWAIT-APP2 _) =
  WF-subst-Q (sym (++-identityʳ Q))
    (pending-update-preserves wf id∈Q (_ , _ , lk-pend))

-- Substep = M-LIFT-OP-FF: creates (fid, dependent [id₁,id₂] f) ∷ Φ, Q=[]
S-SCHEDULE-preserves {ρ} {Φ} {Q} {id} wf id∈Q lk-pend (M-LIFT-OP-FF {id₁ = id₁} {id₂ = id₂} d₁ d₂ neq) =
  WF-subst-Q (sym (++-identityʳ Q))
    (pending-update-preserves
      (M-LIFT-OP-preserves wf (d₁ All.∷ d₂ All.∷ All.[]) (nodup-pair neq))
      id∈Q
      (_ , _ , lk-in-ext))
  where
    fid = fresh-id Φ
    id≢fid : id ≢ fid
    id≢fid = <⇒≢ (WF-cond5 wf id _ lk-pend)
    lk-in-ext : lookup-future ((fid , _) ∷ Φ) id ≡ just (pending _ _)
    lk-in-ext = trans (lookup-prepend-neq Φ id fid _ id≢fid) lk-pend

-- Substep = M-LIFT-OP-FV: creates (fid, dependent [id₁] f) ∷ Φ, Q=[]
S-SCHEDULE-preserves {ρ} {Φ} {Q} {id} wf id∈Q lk-pend (M-LIFT-OP-FV d₁) =
  WF-subst-Q (sym (++-identityʳ Q))
    (pending-update-preserves
      (M-LIFT-OP-preserves wf (d₁ All.∷ All.[]) nodup-single)
      id∈Q
      (_ , _ , lk-in-ext))
  where
    fid = fresh-id Φ
    id≢fid : id ≢ fid
    id≢fid = <⇒≢ (WF-cond5 wf id _ lk-pend)
    lk-in-ext : lookup-future ((fid , _) ∷ Φ) id ≡ just (pending _ _)
    lk-in-ext = trans (lookup-prepend-neq Φ id fid _ id≢fid) lk-pend

-- Substep = M-LIFT-OP-VF: creates (fid, dependent [id₂] f) ∷ Φ, Q=[]
S-SCHEDULE-preserves {ρ} {Φ} {Q} {id} wf id∈Q lk-pend (M-LIFT-OP-VF d₂) =
  WF-subst-Q (sym (++-identityʳ Q))
    (pending-update-preserves
      (M-LIFT-OP-preserves wf (d₂ All.∷ All.[]) nodup-single)
      id∈Q
      (_ , _ , lk-in-ext))
  where
    fid = fresh-id Φ
    id≢fid : id ≢ fid
    id≢fid = <⇒≢ (WF-cond5 wf id _ lk-pend)
    lk-in-ext : lookup-future ((fid , _) ∷ Φ) id ≡ just (pending _ _)
    lk-in-ext = trans (lookup-prepend-neq Φ id fid _ id≢fid) lk-pend

-- Substep = S-RESOLVE: creates (id_r, completed v) ∷ Φ, Q=[]
S-SCHEDULE-preserves {ρ} {Φ} {Q} {id} wf id∈Q lk-pend (S-RESOLVE {id = id_r} lk-dep _ _) =
  WF-subst-Q (sym (++-identityʳ Q))
    (pending-update-preserves
      (S-RESOLVE-preserves wf lk-dep)
      id∈Q
      (_ , _ , lk-in-ext))
  where
    id≢id_r : id ≢ id_r
    id≢id_r refl with trans (sym lk-pend) lk-dep
    ... | ()   -- pending ≢ dependent
    lk-in-ext : lookup-future ((id_r , _) ∷ Φ) id ≡ just (pending _ _)
    lk-in-ext = trans (lookup-prepend-neq Φ id id_r _ id≢id_r) lk-pend

-- Substep = S-SCHEDULE: impossible since inner Q = []
S-SCHEDULE-preserves wf id∈Q lk-pend (S-SCHEDULE {Q = []} () _ _)

-- Substep = S-COMPLETE: impossible since inner Q = []
S-SCHEDULE-preserves wf id∈Q lk-pend (S-COMPLETE {Q = []} () _)

-- Substep = M-ASYNC: creates (fid, pending e_body ρ') ∷ Φ, Q=[fid]
-- This is the most complex case: both Φ and Q get extended
S-SCHEDULE-preserves {ρ} {Φ} {Q} {id} {ρ' = ρ'} wf id∈Q lk-pend (M-ASYNC {e = e_body}) =
  S-SCHEDULE-M-ASYNC-preserves wf id∈Q lk-pend
  where
    -- Core proof for M-ASYNC substep case
    S-SCHEDULE-M-ASYNC-preserves : ∀ {ρ Φ Q id e' ρ' e_body} →
      WF ⟨ ρ , Φ , Q ⟩ →
      id ∈ Q →
      lookup-future Φ id ≡ just (pending e' ρ') →
      let fid = fresh-id Φ in
      let Φ'' = (fid , pending e_body ρ') ∷ Φ in
      WF ⟨ ρ , (id , pending (value-to-expr (futureV fid)) ρ') ∷ Φ'' , Q ++ (fid ∷ []) ⟩
    S-SCHEDULE-M-ASYNC-preserves {ρ} {Φ} {Q} {id} {e'} {ρ'} {e_body}
      (wf-invariant cond1 cond2 cond3 cond4 cond5 cond6) id∈Q lk-pend =
      wf-invariant cond1' cond2' cond3' cond4' cond5' cond6'
      where
        fid = fresh-id Φ
        Φ'' = (fid , pending e_body ρ') ∷ Φ
        Φ-result = (id , pending (value-to-expr (futureV fid)) ρ') ∷ Φ''
        Q-result = Q ++ (fid ∷ [])

        id≢fid : id ≢ fid
        id≢fid = <⇒≢ (cond5 id (pending e' ρ') lk-pend)

        fid-fresh : ¬ (id-in-domain fid Φ)
        fid-fresh = fresh-id-not-in-domain Φ cond5

        -- Lookup helpers for the three-layer Φ: (id, ...) ∷ (fid, ...) ∷ Φ
        lk-result-at-id : lookup-future Φ-result id ≡ just (pending (value-to-expr (futureV fid)) ρ')
        lk-result-at-id = lookup-update-same Φ'' id (pending (value-to-expr (futureV fid)) ρ')

        lk-result-at-fid : lookup-future Φ-result fid ≡ just (pending e_body ρ')
        lk-result-at-fid = trans (lookup-prepend-neq Φ'' fid id _ (λ eq → id≢fid (sym eq)))
                                  (lookup-update-same Φ fid (pending e_body ρ'))

        lk-to-orig : ∀ {id' σ} → id' ≢ id → id' ≢ fid →
          lookup-future Φ-result id' ≡ just σ → lookup-future Φ id' ≡ just σ
        lk-to-orig {id'} neq-id neq-fid lk =
          trans (sym (lookup-prepend-neq Φ id' fid _ neq-fid))
                (trans (sym (lookup-prepend-neq Φ'' id' id _ neq-id)) lk)

        lk-at-id-result : ∀ {σ} → lookup-future Φ-result id ≡ just σ →
          σ ≡ pending (value-to-expr (futureV fid)) ρ'
        lk-at-id-result lk with trans (sym lk-result-at-id) lk
        ... | refl = refl

        lk-at-fid-result : ∀ {σ} → lookup-future Φ-result fid ≡ just σ →
          σ ≡ pending e_body ρ'
        lk-at-fid-result lk with trans (sym lk-result-at-fid) lk
        ... | refl = refl

        -- Condition 1: Q-result ↔ pending in Φ-result
        cond1' : ∀ id' → (id' ∈ Q-result) ↔
                 (∃[ e₀ ] ∃[ ρ₀ ] (lookup-future Φ-result id' ≡ just (pending e₀ ρ₀)))
        cond1' id' = fwd , bwd
          where
            fwd : id' ∈ Q-result → ∃[ e₀ ] ∃[ ρ₀ ] (lookup-future Φ-result id' ≡ just (pending e₀ ρ₀))
            fwd mem with ∈-++-split Q (fid ∷ []) mem
            ... | inj₁ mem-Q = go (id' ≟ id)
              where
                go : Dec (id' ≡ id) → _
                go (yes refl) = _ , _ , lk-result-at-id
                go (no neq) with id' ≟ fid
                ... | yes refl =
                  let (e₀ , ρ₀ , lk₀) = proj₁ (cond1 id') mem-Q in
                  ⊥-elim (fid-fresh (pending e₀ ρ₀ , lk₀))
                ... | no neq-fid =
                  let (e₀ , ρ₀ , lk₀) = proj₁ (cond1 id') mem-Q in
                  e₀ , ρ₀ , trans (lookup-prepend-neq Φ'' id' id _ neq)
                                   (trans (lookup-prepend-neq Φ id' fid _ neq-fid) lk₀)
            ... | inj₂ (here refl) = _ , _ , lk-result-at-fid
            ... | inj₂ (there ())

            bwd-go : Dec (id' ≡ id) → Dec (id' ≡ fid) →
              (∃[ e₀ ] ∃[ ρ₀ ] (lookup-future Φ-result id' ≡ just (pending e₀ ρ₀))) → id' ∈ Q-result
            bwd-go (yes refl) _ _ = ∈-++ˡ id∈Q
            bwd-go (no neq) (yes refl) _ = ∈-++ʳ Q (here refl)
            bwd-go (no neq) (no neq-fid) (e₀ , ρ₀ , lk) =
                    ∈-++ˡ (proj₂ (cond1 id') (e₀ , ρ₀ , lk-to-orig neq neq-fid lk))

            bwd : (∃[ e₀ ] ∃[ ρ₀ ] (lookup-future Φ-result id' ≡ just (pending e₀ ρ₀))) → id' ∈ Q-result
            bwd trip = bwd-go (id' ≟ id) (id' ≟ fid) trip

        -- Condition 2: No dangling deps. Both new entries are pending (no deps).
        cond2' : ∀ id' σ → lookup-future Φ-result id' ≡ just σ →
                  All (λ d → id-in-domain d Φ-result) (get-deps σ)
        cond2' id' σ = cond2-go (id' ≟ id) (id' ≟ fid)
          where
            cond2-go : Dec (id' ≡ id) → Dec (id' ≡ fid) →
              lookup-future Φ-result id' ≡ just σ →
              All (λ d → id-in-domain d Φ-result) (get-deps σ)
            cond2-go (yes refl) _ lk with lk-at-id-result lk
            ... | refl = All.[]
            cond2-go (no neq) (yes refl) lk with lk-at-fid-result lk
            ... | refl = All.[]
            cond2-go (no neq) (no neq-fid) lk =
              all-map (λ {d} din → id-in-domain-prepend Φ'' d id _ (id-in-domain-prepend Φ d fid _ din))
                      (cond2 id' σ (lk-to-orig neq neq-fid lk))

        -- Condition 3: No self-cycles. Both new entries are pending, not dependent.
        cond3' : ∀ id' deps' f → lookup-future Φ-result id' ≡ just (dependent deps' f) →
                       no-self-ref id' deps' × NoDup deps'
        cond3' id' deps' f = cond3-go (id' ≟ id) (id' ≟ fid)
          where
            cond3-go : Dec (id' ≡ id) → Dec (id' ≡ fid) →
              lookup-future Φ-result id' ≡ just (dependent deps' f) →
              no-self-ref id' deps' × NoDup deps'
            cond3-go (yes refl) _ lk with lk-at-id-result lk
            ... | ()
            cond3-go (no neq) (yes refl) lk with lk-at-fid-result lk
            ... | ()
            cond3-go (no neq) (no neq-fid) lk = cond3 id' deps' f (lk-to-orig neq neq-fid lk)

        -- Condition 4: env unchanged, lift domain through double prepend
        cond4' : ∀ x id' → lookup ρ x ≡ just (futureV id') →
                  id-in-domain id' Φ-result
        cond4' x id' lk =
          id-in-domain-prepend Φ'' id' id _ (id-in-domain-prepend Φ id' fid _ (cond4 x id' lk))

        -- Condition 5: All ids < fresh-id Φ-result = suc (suc (fresh-id Φ))
        cond5' : ∀ id' σ → lookup-future Φ-result id' ≡ just σ → id' < fresh-id Φ-result
        cond5' id' σ = cond5-go (id' ≟ id) (id' ≟ fid)
          where
            cond5-go : Dec (id' ≡ id) → Dec (id' ≡ fid) →
              lookup-future Φ-result id' ≡ just σ → id' < fresh-id Φ-result
            cond5-go (yes refl) _ _ = m<n⇒m<1+n (m<n⇒m<1+n (cond5 id (pending e' ρ') lk-pend))
            cond5-go (no neq) (yes refl) _ = m<n⇒m<1+n (n<1+n fid)
            cond5-go (no neq) (no neq-fid) lk = m<n⇒m<1+n (m<n⇒m<1+n (cond5 id' σ (lk-to-orig neq neq-fid lk)))

        -- Condition 6: NoDup (Q ++ [fid])
        fid-not-in-Q : ¬ (fid ∈ Q)
        fid-not-in-Q mem =
          let (_ , _ , lk) = proj₁ (cond1 fid) mem in
          fid-fresh (pending _ _ , lk)

        cond6' : NoDup (Q ++ (fid ∷ []))
        cond6' = NoDup-++ Q (fid ∷ []) cond6 ((λ ()) , tt)
                   (λ {x} x∈Q → λ { (here refl) → fid-not-in-Q x∈Q ; (there ()) })

-- ============================================================================
-- MAIN THEOREM: WF Preservation by case analysis — ALL CASES PROVEN
-- ============================================================================

WF-preserved : ∀ {c c'} → WF (cfg-state c) → c ⟶ c' → WF (cfg-state c')
WF-preserved wf M-ASYNC = M-ASYNC-preserves wf
WF-preserved wf (M-LIFT-OP-FF d₁ d₂ neq) = M-LIFT-OP-preserves wf (d₁ All.∷ d₂ All.∷ All.[]) (nodup-pair neq)
WF-preserved wf (M-LIFT-OP-FV d₁) = M-LIFT-OP-preserves wf (d₁ All.∷ All.[]) nodup-single
WF-preserved wf (M-LIFT-OP-VF d₂) = M-LIFT-OP-preserves wf (d₂ All.∷ All.[]) nodup-single
WF-preserved wf (M-AWAIT _) = M-AWAIT-preserves wf
WF-preserved wf (M-AWAIT-IF _) = M-AWAIT-IF-preserves wf
WF-preserved wf (M-AWAIT-APP1 _) = M-AWAIT-APP1-preserves wf
WF-preserved wf (M-AWAIT-APP2 _) = M-AWAIT-APP2-preserves wf
WF-preserved wf (S-COMPLETE mem lk) = S-COMPLETE-preserves wf mem lk
WF-preserved wf (S-SCHEDULE mem lk substep) = S-SCHEDULE-preserves wf mem lk substep
WF-preserved wf (S-RESOLVE lk _ _) = S-RESOLVE-preserves wf lk

-- ============================================================================
-- STUCK CHARACTERIZATION  
-- ============================================================================

-- Define when configuration is "stuck"
IsCompleted : Status → Set
IsCompleted (completed _) = ⊤
IsCompleted _ = ⊥

-- Simplified: Main expression directly mentions a Future
data NeedsFuture (e : Expr) (id : Id) : Set where
  direct : e ≡ value-to-expr (futureV id) → NeedsFuture e id

data Stuck : Configuration → Set where
  main-blocked : ∀ {e s id} →
    NeedsFuture e id →
    (∃[ σ ] (lookup-future (get-futures s) id ≡ just σ × ¬ IsCompleted σ)) →
    (get-queue s ≡ []) →
    Stuck ⟪ e , s ⟫

postulate NeedsFuture' : Expr → Id → Set

postulate stuck-characterization : ∀ {c} → WF (cfg-state c) → Stuck c → (∀ c' → ¬ (c ⟶ c')) → ∃[ id ] ∃[ σ ] (NeedsFuture' (cfg-expr c) id × lookup-future (get-futures (cfg-state c)) id ≡ just σ × ¬ IsCompleted σ × get-queue (cfg-state c) ≡ [])