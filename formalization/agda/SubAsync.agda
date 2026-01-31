-- Sub_Async: Untyped operational semantics mechanization in Agda
-- Following the structure from SLIDES_CORE_RULES.md

open import Data.Nat using (ℕ; zero; suc; _+_; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥; ⊥-elim)

module SubAsync where

-- BASIC TYPES
Id : Set
Id = ℕ  -- Future ids are natural numbers

-- EXPRESSIONS (Abstract Syntax from slides)
data Op : Set where
  add sub mul div : Op
  lt  eq         : Op

-- Variables as strings (simplified)
postulate Var : Set
postulate _≟ᵥ_ : (x y : Var) → Dec (x ≡ y)

mutual
  data Expr : Set where
    -- Basic values
    var   : Var → Expr
    num   : ℕ → Expr  
    bool  : Bool → Expr
    
    -- Operations
    binop : Op → Expr → Expr → Expr
    
    -- Control flow
    if_then_else : Expr → Expr → Expr → Expr
    
    -- Functions
    fun   : Var → Expr → Expr
    app   : Expr → Expr → Expr
    
    -- Let binding  
    let⟨_⟩=_⟨in⟩_ : Var → Expr → Expr → Expr
    
    -- Async
    async : Expr → Expr

mutual
  -- VALUES (runtime values)
  data Value : Set where
    numV  : ℕ → Value
    boolV : Bool → Value
    funV  : Var → Expr → Env → Value  -- closure
    futureV : Id → Value

  -- ENVIRONMENT (maps variables to values)  
  Env : Set
  Env = List (Var × Value)

-- Environment lookup
lookup : Env → Var → Maybe Value
lookup [] x = nothing
lookup ((y , v) ∷ env) x with x ≟ᵥ y
... | yes _ = just v
... | no  _ = lookup env x

-- FUTURE STATUS (from slides)
data Status : Set where
  pending   : Expr → Env → Status
  completed : Value → Status
  dependent : List Id → (List Value → Value) → Status

-- Note: combine function (List Value → Value) is postulated
-- In real implementation, this would be constructed by M-LIFT-OP rules
postulate CombineFunction : Set
postulate apply-combine : CombineFunction → List Value → Value

-- FUTURE TABLE (maps ids to status)
FutureTable : Set  
FutureTable = List (Id × Status)

-- Future table lookup
lookup-future : FutureTable → Id → Maybe Status
lookup-future [] id = nothing
lookup-future ((id' , σ) ∷ Φ) id with id ≟ id'
... | yes _ = just σ
... | no  _ = lookup-future Φ id

-- PENDING QUEUE
PendingQueue : Set
PendingQueue = List Id

-- STATE COMPONENTS
record State : Set where
  constructor ⟨_,_,_⟩
  field
    ρ : Env           -- environment
    Φ : FutureTable   -- future table  
    Q : PendingQueue  -- pending queue

-- CONFIGURATION (use record to avoid parser ambiguity with State constructor)
record Configuration : Set where
  constructor ⟪_,_⟫
  field
    expr  : Expr
    state : State

-- Projection helpers
get-env : State → Env
get-env = State.ρ

get-futures : State → FutureTable  
get-futures = State.Φ

get-queue : State → PendingQueue
get-queue = State.Q

cfg-expr : Configuration → Expr
cfg-expr = Configuration.expr

cfg-state : Configuration → State
cfg-state = Configuration.state