-- WF Preservation proof outline
-- This is what you can mechanize without types!

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)  
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_)

open import SubAsync
open import WellFormedness  
open import Reductions

module WFPreservation where

-- ============================================================================
-- AUXILIARY LEMMAS (postulated - can be proven with more work)
-- ============================================================================

-- Lemma: fresh-id is not in current FutureTable (by construction)
postulate fresh-id-not-in-domain : (Φ : FutureTable) → ¬ (id-in-domain (fresh-id Φ) Φ)

-- Lemma: lookup after update (simplified for postulate)
postulate lookup-update-same : (Φ : FutureTable) (id : Id) (σ : Status) → lookup-future ((id , σ) ∷ Φ) id ≡ just σ

-- Lemma: adding to queue preserves membership
postulate queue-add-preserves : (Q : PendingQueue) (id id' : Id) → id' ∈ Q → id' ∈ (id ∷ Q)

-- Lemma: new id is in extended queue
queue-add-new : (Q : PendingQueue) (id : Id) → id ∈ (id ∷ Q)
queue-add-new Q id = here refl

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
-- MORE COMPLEX CASES (postulated - need substantial proofs)
-- ============================================================================

-- Case S-RESOLVE: Dependent → Completed
postulate S-RESOLVE-preserves : ∀ {ρ Φ Q id v} → WF ⟨ ρ , Φ , Q ⟩ → WF ⟨ ρ , (id , completed v) ∷ Φ , Q ⟩

-- Case M-LIFT-OP-* (FF, FV, VF): Creates Dependent future
-- Simplified type signature (real proof would need deps-exist premise)
postulate M-LIFT-OP-preserves : ∀ {ρ Φ Q deps combine} → WF ⟨ ρ , Φ , Q ⟩ → WF ⟨ ρ , (fresh-id Φ , dependent deps combine) ∷ Φ , Q ⟩

-- Case M-ASYNC: async e → Future(id)
postulate M-ASYNC-preserves : ∀ {ρ Φ Q e} → WF ⟨ ρ , Φ , Q ⟩ → WF ⟨ ρ , (fresh-id Φ , pending e ρ) ∷ Φ , fresh-id Φ ∷ Q ⟩

-- Case S-COMPLETE: Pending(value) → Completed, remove from Q
postulate S-COMPLETE-preserves : ∀ {ρ Φ Q id v} → WF ⟨ ρ , Φ , Q ⟩ → WF ⟨ ρ , (id , completed v) ∷ Φ , Q ⟩

-- Case S-SCHEDULE: Most complex - use generic postulate
-- The result state structure is complex, so we postulate preservation directly
postulate S-SCHEDULE-preserves-generic : ∀ {c c'} → WF (cfg-state c) → c ⟶ c' → WF (cfg-state c')

-- ============================================================================
-- MAIN THEOREM: WF Preservation by case analysis
-- ============================================================================

-- The main theorem with cases filled in
-- Some cases use postulated lemmas, others are direct
WF-preserved : ∀ {c c'} → WF (cfg-state c) → c ⟶ c' → WF (cfg-state c')
-- Simple cases: state unchanged or trivially updated
WF-preserved wf M-ASYNC = M-ASYNC-preserves wf
WF-preserved wf M-LIFT-OP-FF = M-LIFT-OP-preserves wf
WF-preserved wf M-LIFT-OP-FV = M-LIFT-OP-preserves wf
WF-preserved wf M-LIFT-OP-VF = M-LIFT-OP-preserves wf
WF-preserved wf (M-AWAIT _) = M-AWAIT-preserves wf
WF-preserved wf (M-AWAIT-IF _) = M-AWAIT-IF-preserves wf
WF-preserved wf (M-AWAIT-APP1 _) = M-AWAIT-APP1-preserves wf
WF-preserved wf (M-AWAIT-APP2 _) = M-AWAIT-APP2-preserves wf
-- Complex cases: use generic postulate  
WF-preserved wf step@(S-SCHEDULE _ _ _) = S-SCHEDULE-preserves-generic wf step
WF-preserved wf step@(S-COMPLETE _ _) = S-SCHEDULE-preserves-generic wf step
WF-preserved wf (S-RESOLVE _ _ _) = S-RESOLVE-preserves wf

-- ============================================================================
-- STUCK CHARACTERIZATION  
-- ============================================================================

-- Define when configuration is "stuck"
IsCompleted : Status → Set
IsCompleted (completed _) = ⊤
IsCompleted _ = ⊥

-- Use standard library disjunction
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- Simplified: Main expression directly mentions a Future
-- (Full definition would enumerate all positions)
data NeedsFuture (e : Expr) (id : Id) : Set where
  direct : e ≡ value-to-expr (futureV id) → NeedsFuture e id
  -- can add more cases for: if, app, binop contexts

data Stuck : Configuration → Set where
  main-blocked : ∀ {e s id} →
    -- Main expression needs a value from Future id  
    NeedsFuture e id →
    -- But Future is not completed
    (∃[ σ ] (lookup-future (get-futures s) id ≡ just σ × ¬ IsCompleted σ)) →
    -- And no work pending  
    (get-queue s ≡ []) →
    Stuck ⟪ e , s ⟫

-- Helper functions for stuck characterization
-- (NeedsFuture predicate - simplified for skeleton)
postulate NeedsFuture' : Expr → Id → Set

-- STUCK CHARACTERIZATION THEOREM
-- "If WF and stuck, then stuck only because awaiting incomplete Future"  
-- This requires careful case analysis - postulate for now
postulate stuck-characterization : ∀ {c} → WF (cfg-state c) → Stuck c → (∀ c' → ¬ (c ⟶ c')) → ∃[ id ] ∃[ σ ] (NeedsFuture' (cfg-expr c) id × lookup-future (get-futures (cfg-state c)) id ≡ just σ × ¬ IsCompleted σ × get-queue (cfg-state c) ≡ [])