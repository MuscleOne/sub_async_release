-- Examples: Concrete execution traces for validation
-- Based on actual OCaml execution output
--
-- Example 1 (01_basic.sub):
--   let x = async (2 + 3) in      # Future #0
--   let y = async (10 * 10) in    # Future #1  
--   let z = async (7 * 8) in      # Future #2
--   x + y + z                     # Future #3 (x+y), Future #4 (result)
--
-- Example 2 (11_diamond_dependency.sub):
--   let x = async 1000 in         # Future #0 (root)
--   let left = x + 1 in           # Future #1 depends on [0]
--   let right = x + 2 in          # Future #2 depends on [0]
--   left + right                  # Future #3 depends on [1, 2]

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (here; there)  -- for ∈Q proofs
open import Data.Maybe using (just; nothing)
open import Data.String using (String)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import SubAsync
open import WellFormedness
open import Reductions

module Examples where

-- Helpers for constructing examples
postulate varX varY varZ varLeft varRight : Var

-- =============================================================================
-- EXAMPLE 1: 01_basic.sub 
-- =============================================================================

-- Initial: just the first async
example1-step0 : Configuration
example1-step0 = ⟪ async (binop add (num 2) (num 3)) , ⟨ [] , [] , [] ⟩ ⟫

-- After first M-ASYNC: Future #0 created  
ft1 : FutureTable
ft1 = (0 , pending (binop add (num 2) (num 3)) []) ∷ []

example1-step1 : Configuration
example1-step1 = ⟪ value-to-expr (futureV 0) , ⟨ [] , ft1 , 0 ∷ [] ⟩ ⟫

-- After all 3 async are created
ft3 : FutureTable
ft3 = (0 , pending (binop add (num 2) (num 3)) []) ∷
      (1 , pending (binop mul (num 10) (num 10)) []) ∷
      (2 , pending (binop mul (num 7) (num 8)) []) ∷
      []

env3 : Env
env3 = (varX , futureV 0) ∷ (varY , futureV 1) ∷ (varZ , futureV 2) ∷ []

example1-after-3-async : Configuration
example1-after-3-async = ⟪ value-to-expr (futureV 0) , ⟨ env3 , ft3 , 0 ∷ 1 ∷ 2 ∷ [] ⟩ ⟫

-- After M-LIFT-OP creates Future #3 for x+y
ft4 : FutureTable
ft4 = (0 , pending (binop add (num 2) (num 3)) []) ∷
      (1 , pending (binop mul (num 10) (num 10)) []) ∷
      (2 , pending (binop mul (num 7) (num 8)) []) ∷
      (3 , dependent (0 ∷ 1 ∷ []) (combine-binary add)) ∷
      []

example1-after-lift-xy : Configuration  
example1-after-lift-xy = ⟪ value-to-expr (futureV 3) , ⟨ env3 , ft4 , 0 ∷ 1 ∷ 2 ∷ [] ⟩ ⟫

-- After M-LIFT-OP creates Future #4 for (#3+z)
ft5 : FutureTable
ft5 = (0 , pending (binop add (num 2) (num 3)) []) ∷
      (1 , pending (binop mul (num 10) (num 10)) []) ∷
      (2 , pending (binop mul (num 7) (num 8)) []) ∷
      (3 , dependent (0 ∷ 1 ∷ []) (combine-binary add)) ∷
      (4 , dependent (3 ∷ 2 ∷ []) (combine-binary add)) ∷
      []

example1-after-lift-final : Configuration
example1-after-lift-final = ⟪ value-to-expr (futureV 4) , ⟨ env3 , ft5 , 0 ∷ 1 ∷ 2 ∷ [] ⟩ ⟫

-- After S-COMPLETE for Future #0: 2+3 = 5
ft6 : FutureTable
ft6 = (0 , completed (numV 5)) ∷
      (1 , pending (binop mul (num 10) (num 10)) []) ∷
      (2 , pending (binop mul (num 7) (num 8)) []) ∷
      (3 , dependent (0 ∷ 1 ∷ []) (combine-binary add)) ∷
      (4 , dependent (3 ∷ 2 ∷ []) (combine-binary add)) ∷
      []

example1-after-complete-0 : Configuration
example1-after-complete-0 = ⟪ value-to-expr (futureV 4) , ⟨ env3 , ft6 , 1 ∷ 2 ∷ [] ⟩ ⟫

-- After S-COMPLETE for Future #1: 10*10 = 100
ft7 : FutureTable
ft7 = (0 , completed (numV 5)) ∷
      (1 , completed (numV 100)) ∷
      (2 , pending (binop mul (num 7) (num 8)) []) ∷
      (3 , dependent (0 ∷ 1 ∷ []) (combine-binary add)) ∷
      (4 , dependent (3 ∷ 2 ∷ []) (combine-binary add)) ∷
      []

example1-after-complete-1 : Configuration
example1-after-complete-1 = ⟪ value-to-expr (futureV 4) , ⟨ env3 , ft7 , 2 ∷ [] ⟩ ⟫

-- Final state: all resolved, result = 161
ft-final : FutureTable
ft-final = (0 , completed (numV 5)) ∷
           (1 , completed (numV 100)) ∷
           (2 , completed (numV 56)) ∷
           (3 , completed (numV 105)) ∷
           (4 , completed (numV 161)) ∷
           []

example1-final : Configuration
example1-final = ⟪ value-to-expr (futureV 4) , ⟨ env3 , ft-final , [] ⟩ ⟫

-- =============================================================================
-- EXAMPLE 2: 11_diamond_dependency.sub (DIAMOND PATTERN)
-- =============================================================================

-- Initial: async 1000
example2-step0 : Configuration
example2-step0 = ⟪ async (num 1000) , ⟨ [] , [] , [] ⟩ ⟫

-- After M-ASYNC: Future #0 created
ft2-1 : FutureTable
ft2-1 = (0 , pending (num 1000) []) ∷ []

example2-step1 : Configuration
example2-step1 = ⟪ value-to-expr (futureV 0) , ⟨ [] , ft2-1 , 0 ∷ [] ⟩ ⟫

-- After creating dependent Future #1 (x + 1)
env2-1 : Env
env2-1 = (varX , futureV 0) ∷ []

ft2-2 : FutureTable
ft2-2 = (0 , pending (num 1000) []) ∷
        (1 , dependent (0 ∷ []) (combine-unary-left add (numV 1))) ∷
        []

example2-after-lift-1 : Configuration
example2-after-lift-1 = ⟪ value-to-expr (futureV 1) , ⟨ env2-1 , ft2-2 , 0 ∷ [] ⟩ ⟫

-- After creating dependent Future #2 (x + 2)
env2-2 : Env
env2-2 = (varX , futureV 0) ∷ (varLeft , futureV 1) ∷ []

ft2-3 : FutureTable
ft2-3 = (0 , pending (num 1000) []) ∷
        (1 , dependent (0 ∷ []) (combine-unary-left add (numV 1))) ∷
        (2 , dependent (0 ∷ []) (combine-unary-left add (numV 2))) ∷
        []

example2-after-lift-2 : Configuration
example2-after-lift-2 = ⟪ value-to-expr (futureV 2) , ⟨ env2-2 , ft2-3 , 0 ∷ [] ⟩ ⟫

-- After creating dependent Future #3 (left + right) - THE DIAMOND!
env2-3 : Env
env2-3 = (varX , futureV 0) ∷ (varLeft , futureV 1) ∷ (varRight , futureV 2) ∷ []

ft2-4 : FutureTable
ft2-4 = (0 , pending (num 1000) []) ∷
        (1 , dependent (0 ∷ []) (combine-unary-left add (numV 1))) ∷
        (2 , dependent (0 ∷ []) (combine-unary-left add (numV 2))) ∷
        (3 , dependent (1 ∷ 2 ∷ []) (combine-binary add)) ∷
        []

example2-after-lift-3 : Configuration
example2-after-lift-3 = ⟪ value-to-expr (futureV 3) , ⟨ env2-3 , ft2-4 , 0 ∷ [] ⟩ ⟫

-- After S-COMPLETE for Future #0: 1000
ft2-5 : FutureTable
ft2-5 = (0 , completed (numV 1000)) ∷
        (1 , dependent (0 ∷ []) (combine-unary-left add (numV 1))) ∷
        (2 , dependent (0 ∷ []) (combine-unary-left add (numV 2))) ∷
        (3 , dependent (1 ∷ 2 ∷ []) (combine-binary add)) ∷
        []

example2-after-complete-0 : Configuration
example2-after-complete-0 = ⟪ value-to-expr (futureV 3) , ⟨ env2-3 , ft2-5 , [] ⟩ ⟫

-- Final state after all S-RESOLVE: result = 2003
ft2-final : FutureTable
ft2-final = (0 , completed (numV 1000)) ∷
            (1 , completed (numV 1001)) ∷
            (2 , completed (numV 1002)) ∷
            (3 , completed (numV 2003)) ∷
            []

example2-final : Configuration
example2-final = ⟪ value-to-expr (futureV 3) , ⟨ env2-3 , ft2-final , [] ⟩ ⟫

-- =============================================================================
-- PROOF ATTEMPTS 
-- =============================================================================

-- Example 1: First step: async e → Future(0)
example1-step0→1 : example1-step0 ⟶ example1-step1  
example1-step0→1 = M-ASYNC

-- Example 2: First step: async 1000 → Future(0)
example2-step0→1 : example2-step0 ⟶ example2-step1
example2-step0→1 = M-ASYNC
-- =============================================================================
-- M-LIFT-OP-FF PROOF: Future #0 + Future #1 → Future #3
-- =============================================================================

-- Configuration: binop add (Future 0) (Future 1) with ft3 
-- Result: new dependent Future #3

lift-ff-before : Configuration
lift-ff-before = ⟪ binop add (value-to-expr (futureV 0)) (value-to-expr (futureV 1)) 
                 , ⟨ env3 , ft3 , 0 ∷ 1 ∷ 2 ∷ [] ⟩ ⟫

-- After M-LIFT-OP-FF: fresh-id ft3 = 3
-- NOTE: update-future adds to FRONT of list!
ft4' : FutureTable
ft4' = (3 , dependent (0 ∷ 1 ∷ []) (combine-binary add)) ∷
       (0 , pending (binop add (num 2) (num 3)) []) ∷
       (1 , pending (binop mul (num 10) (num 10)) []) ∷
       (2 , pending (binop mul (num 7) (num 8)) []) ∷
       []

lift-ff-after : Configuration
lift-ff-after = ⟪ value-to-expr (futureV 3) , ⟨ env3 , ft4' , 0 ∷ 1 ∷ 2 ∷ [] ⟩ ⟫

-- The proof!
lift-ff-proof : lift-ff-before ⟶ lift-ff-after
lift-ff-proof = M-LIFT-OP-FF

-- =============================================================================
-- S-COMPLETE PROOF: Pending(value) → Completed
-- =============================================================================

-- Setup: Future #0 has pending expression that is already a value (num 5)
-- This represents the moment when evaluation of 2+3 has finished

ft-pending-value : FutureTable
ft-pending-value = (0 , pending (num 5) []) ∷ []  -- num 5 = value-to-expr (numV 5)

complete-before : Configuration
complete-before = ⟪ num 99 , ⟨ [] , ft-pending-value , 0 ∷ [] ⟩ ⟫  -- main expr doesn't matter

-- After S-COMPLETE: 
--   1. remove-from-queue removes 0 from Q → []
--   2. update-future ADDS (0, completed) to FRONT of Φ
-- So result has TWO entries for id 0 (old pending + new completed)
ft-completed : FutureTable  
ft-completed = (0 , completed (numV 5)) ∷ (0 , pending (num 5) []) ∷ []

complete-after : Configuration
complete-after = ⟪ num 99 , ⟨ [] , ft-completed , [] ⟩ ⟫

-- Membership proof: 0 is in queue [0]
0∈Q : 0 ∈Q (0 ∷ [])
0∈Q = here refl

-- Lookup proof: looking up Future #0 returns pending (num 5)
lookup-0-pending : lookup-future ft-pending-value 0 ≡ just (pending (num 5) [])
lookup-0-pending = refl

-- The proof!
complete-proof : complete-before ⟶ complete-after
complete-proof = S-COMPLETE 0∈Q lookup-0-pending

-- =============================================================================
-- M-AWAIT PROOF: Extract value from completed Future
-- =============================================================================

-- Setup: Future #0 is completed with value 42
ft-with-completed : FutureTable
ft-with-completed = (0 , completed (numV 42)) ∷ []

await-before : Configuration
await-before = ⟪ value-to-expr (futureV 0) , ⟨ [] , ft-with-completed , [] ⟩ ⟫

await-after : Configuration
await-after = ⟪ value-to-expr (numV 42) , ⟨ [] , ft-with-completed , [] ⟩ ⟫

-- Lookup proof: looking up Future #0 returns completed (numV 42)
lookup-0-completed : lookup-future ft-with-completed 0 ≡ just (completed (numV 42))
lookup-0-completed = refl

-- The proof!
await-proof : await-before ⟶ await-after
await-proof = M-AWAIT lookup-0-completed

-- =============================================================================
-- S-RESOLVE PROOF: Dependent → Completed when all deps are ready
-- =============================================================================

-- Setup: Future #2 depends on [0, 1], both are completed
-- combine-binary add will compute: numV (5 + 10) = numV 15

ft-for-resolve : FutureTable
ft-for-resolve = (0 , completed (numV 5)) ∷
                 (1 , completed (numV 10)) ∷
                 (2 , dependent (0 ∷ 1 ∷ []) (combine-binary add)) ∷
                 []

resolve-before : Configuration
resolve-before = ⟪ num 99 , ⟨ [] , ft-for-resolve , [] ⟩ ⟫

-- After S-RESOLVE: Future #2 becomes completed with combined value
ft-after-resolve : FutureTable
ft-after-resolve = (2 , completed (numV 15)) ∷  -- update adds to front!
                   (0 , completed (numV 5)) ∷
                   (1 , completed (numV 10)) ∷
                   (2 , dependent (0 ∷ 1 ∷ []) (combine-binary add)) ∷
                   []

resolve-after : Configuration
resolve-after = ⟪ num 99 , ⟨ [] , ft-after-resolve , [] ⟩ ⟫

-- Lookup proof
lookup-2-dependent : lookup-future ft-for-resolve 2 ≡ just (dependent (0 ∷ 1 ∷ []) (combine-binary add))
lookup-2-dependent = refl

-- Collect values proof: looking up [0, 1] gives [numV 5, numV 10]
collect-01 : collect-values ft-for-resolve (0 ∷ 1 ∷ []) ≡ just (numV 5 ∷ numV 10 ∷ [])
collect-01 = refl

-- All completed proof
all-completed-01 : all-completed ft-for-resolve (0 ∷ 1 ∷ []) ≡ true
all-completed-01 = refl

-- The proof!
resolve-proof : resolve-before ⟶ resolve-after
resolve-proof = S-RESOLVE lookup-2-dependent collect-01 all-completed-01

-- =============================================================================
-- M-LIFT-OP-FV PROOF: Future + Value → Dependent Future
-- =============================================================================
-- This is for expressions like: x + 1 (where x is Future #0)

-- Setup: Future #0 exists, we compute Future#0 + 5
ft-for-fv : FutureTable
ft-for-fv = (0 , pending (num 1000) []) ∷ []

lift-fv-before : Configuration
lift-fv-before = ⟪ binop add (value-to-expr (futureV 0)) (value-to-expr (numV 5))
                 , ⟨ [] , ft-for-fv , 0 ∷ [] ⟩ ⟫

-- After M-LIFT-OP-FV: fresh-id ft-for-fv = 1
-- Creates dependent Future #1 with deps = [0] and combine-unary-left add (numV 5)
ft-after-fv : FutureTable
ft-after-fv = (1 , dependent (0 ∷ []) (combine-unary-left add (numV 5))) ∷
              (0 , pending (num 1000) []) ∷
              []

lift-fv-after : Configuration
lift-fv-after = ⟪ value-to-expr (futureV 1) , ⟨ [] , ft-after-fv , 0 ∷ [] ⟩ ⟫

-- The proof!
lift-fv-proof : lift-fv-before ⟶ lift-fv-after
lift-fv-proof = M-LIFT-OP-FV

-- =============================================================================
-- M-LIFT-OP-VF PROOF: Value + Future → Dependent Future
-- =============================================================================
-- This is for expressions like: 100 + x (where x is Future #0)

-- Setup: Same FutureTable, but value on left side
lift-vf-before : Configuration
lift-vf-before = ⟪ binop add (value-to-expr (numV 100)) (value-to-expr (futureV 0))
                 , ⟨ [] , ft-for-fv , 0 ∷ [] ⟩ ⟫

-- After M-LIFT-OP-VF: fresh-id ft-for-fv = 1
-- Creates dependent Future #1 with deps = [0] and combine-unary-right add (numV 100)
ft-after-vf : FutureTable
ft-after-vf = (1 , dependent (0 ∷ []) (combine-unary-right add (numV 100))) ∷
              (0 , pending (num 1000) []) ∷
              []

lift-vf-after : Configuration
lift-vf-after = ⟪ value-to-expr (futureV 1) , ⟨ [] , ft-after-vf , 0 ∷ [] ⟩ ⟫

-- The proof!
lift-vf-proof : lift-vf-before ⟶ lift-vf-after
lift-vf-proof = M-LIFT-OP-VF

-- =============================================================================
-- M-AWAIT-IF PROOF: Await in if condition
-- =============================================================================
-- When a Future in if-condition is completed, extract and evaluate

-- Setup: Future #0 is completed with boolV true
ft-for-await-if : FutureTable
ft-for-await-if = (0 , completed (boolV true)) ∷ []

await-if-before : Configuration
await-if-before = ⟪ if (value-to-expr (futureV 0)) then (num 1) else (num 2) 
                  , ⟨ [] , ft-for-await-if , [] ⟩ ⟫

-- After M-AWAIT-IF: eval-if (boolV true) (num 1) (num 2) = num 1
await-if-after : Configuration
await-if-after = ⟪ num 1 , ⟨ [] , ft-for-await-if , [] ⟩ ⟫

-- Lookup proof
lookup-0-bool : lookup-future ft-for-await-if 0 ≡ just (completed (boolV true))
lookup-0-bool = refl

-- The proof!
await-if-proof : await-if-before ⟶ await-if-after
await-if-proof = M-AWAIT-IF lookup-0-bool

-- =============================================================================
-- SEMANTICS vs IMPLEMENTATION NOTE
-- =============================================================================
-- 
-- Our SEMANTIC rules (S-SCHEDULE, S-COMPLETE, S-RESOLVE) use:
--   id ∈Q Q   -- "pick ANY task from queue"
--
-- Our OCaml IMPLEMENTATION (scheduler.ml) uses:
--   run_all()        -- FIFO order
--   run_one_random() -- random selection
--
-- KEY INSIGHT: This is NOT a conflict!
-- - Non-deterministic semantics says "any scheduling is valid"
-- - FIFO is just ONE specific valid scheduling
-- - Random is ANOTHER valid scheduling
--
-- BENEFIT: Proofs hold for ALL possible schedulers!
-- The semantics "over-approximates" all possible executions.
--
-- This is the standard approach: 
--   Semantics = specification (what's allowed)
--   Implementation = refinement (one specific choice)
-- =============================================================================

-- =============================================================================
-- M-AWAIT-APP1 PROOF: Await function position in application
-- =============================================================================
-- When a Future in function position is completed, extract and apply
-- Note: eval-app is postulated, so we just show the rule applies

-- Setup: Future #0 is completed with a function value
postulate testFun : Var  -- dummy variable for function

ft-for-await-app1 : FutureTable
ft-for-await-app1 = (0 , completed (funV testFun (num 42) [])) ∷ []

await-app1-before : Configuration
await-app1-before = ⟪ app (value-to-expr (futureV 0)) (num 10)
                    , ⟨ [] , ft-for-await-app1 , [] ⟩ ⟫

-- After M-AWAIT-APP1: eval-app (funV ...) (num 10)
await-app1-after : Configuration
await-app1-after = ⟪ eval-app (funV testFun (num 42) []) (num 10)
                   , ⟨ [] , ft-for-await-app1 , [] ⟩ ⟫

-- Lookup proof
lookup-0-fun : lookup-future ft-for-await-app1 0 ≡ just (completed (funV testFun (num 42) []))
lookup-0-fun = refl

-- The proof!
await-app1-proof : await-app1-before ⟶ await-app1-after
await-app1-proof = M-AWAIT-APP1 lookup-0-fun

-- =============================================================================
-- M-AWAIT-APP2 PROOF: Await argument position in application  
-- =============================================================================
-- When a Future in argument position is completed, extract and apply

-- Setup: Function value applied to Future #0 which is completed
ft-for-await-app2 : FutureTable
ft-for-await-app2 = (0 , completed (numV 99)) ∷ []

await-app2-before : Configuration
await-app2-before = ⟪ app (value-to-expr (funV testFun (num 42) [])) (value-to-expr (futureV 0))
                    , ⟨ [] , ft-for-await-app2 , [] ⟩ ⟫

-- After M-AWAIT-APP2: eval-app-val (funV ...) (numV 99)
await-app2-after : Configuration
await-app2-after = ⟪ eval-app-val (funV testFun (num 42) []) (numV 99)
                   , ⟨ [] , ft-for-await-app2 , [] ⟩ ⟫

-- Lookup proof
lookup-0-arg : lookup-future ft-for-await-app2 0 ≡ just (completed (numV 99))
lookup-0-arg = refl

-- The proof!
await-app2-proof : await-app2-before ⟶ await-app2-after
await-app2-proof = M-AWAIT-APP2 lookup-0-arg
-- =============================================================================
-- S-SCHEDULE PROOF: Execute one step of pending Future (MOST COMPLEX!)
-- =============================================================================
-- S-SCHEDULE requires:
--   1. id ∈Q Q                    -- task is in queue
--   2. lookup Φ id = pending e ρ  -- task is pending with expression e
--   3. ⟪ e, ⟨ρ, Φ, []⟩ ⟫ ⟶ ⟪ e', s' ⟫  -- NESTED PROOF: e can step
--
-- Scenario: Future #0 has pending expression (async (num 10))
-- The inner async can step via M-ASYNC, creating a new Future

-- Setup: Main expression is (num 99), Future #0 has pending (async (num 10))
ft-for-schedule : FutureTable  
ft-for-schedule = (0 , pending (async (num 10)) []) ∷ []

schedule-before : Configuration
schedule-before = ⟪ num 99 , ⟨ [] , ft-for-schedule , 0 ∷ [] ⟩ ⟫

-- Inner step analysis:
-- The inner async (num 10) executes with: ⟪ async (num 10), ⟨[], Φ, []⟩ ⟫
-- fresh-id Φ = fresh-id [(0,...)] = suc (fresh-id []) = 1
-- M-ASYNC creates:
--   e'' = futureV 1
--   s'' = ⟨ [], (1, pending (num 10) []) ∷ Φ , [1] ⟩

inner-ft-after : FutureTable
inner-ft-after = (1 , pending (num 10) []) ∷ ft-for-schedule

inner-s'' : State
inner-s'' = ⟨ [] , inner-ft-after , 1 ∷ [] ⟩

inner-step-config-after : Configuration
inner-step-config-after = ⟪ value-to-expr (futureV 1) , inner-s'' ⟫

-- The nested proof!
inner-step : ⟪ async (num 10) , ⟨ [] , ft-for-schedule , [] ⟩ ⟫ ⟶ inner-step-config-after
inner-step = M-ASYNC

-- After S-SCHEDULE:
-- merge-futures Φ (get-futures s'') = ft-for-schedule ++ inner-ft-after
-- merge-queues Q (get-queue s'') = [0] ++ [1] = [0, 1]
-- update-future adds (0, pending (futureV 1) []) to front
--
-- WAIT: merge-futures Φ (get-futures s'')
--   = ft-for-schedule ++ inner-ft-after  
--   = [(0, ...)] ++ [(1, ...), (0, ...)]
--   = [(0, ...), (1, ...), (0, ...)]
-- Then update-future prepends (0, pending new-expr [])

ft-merged : FutureTable
ft-merged = ft-for-schedule ++ inner-ft-after  -- merge

-- Result of update-future ... id (pending e'' env'')
ft-after-schedule : FutureTable
ft-after-schedule = (0 , pending (value-to-expr (futureV 1)) []) ∷ ft-merged

schedule-after : Configuration
schedule-after = ⟪ num 99 , ⟨ [] , ft-after-schedule , 0 ∷ 1 ∷ [] ⟩ ⟫

-- Membership proof: 0 is in queue [0]
0∈Q-schedule : 0 ∈Q (0 ∷ [])
0∈Q-schedule = here refl

-- Lookup proof: Future #0 is pending with (async (num 10))
lookup-0-pending-async : lookup-future ft-for-schedule 0 ≡ just (pending (async (num 10)) [])
lookup-0-pending-async = refl

-- The proof!
schedule-proof : schedule-before ⟶ schedule-after
schedule-proof = S-SCHEDULE 0∈Q-schedule lookup-0-pending-async inner-step
