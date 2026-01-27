-- Hello.agda - Your first Agda file
-- Based on: https://agda.readthedocs.io/en/latest/getting-started/hello-world.html

module Hello where

-- Import standard library basics
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Define a simple function
double : ℕ → ℕ
double n = n + n

-- Prove a property about double
_ : double 2 ≡ 4
_ = refl

-- Another simple proof
_ : double 0 ≡ 0
_ = refl

-- Pattern matching on natural numbers
pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

-- Proof using pattern matching result
_ : pred 3 ≡ 2
_ = refl

{- 
To type-check this file:
  agda Hello.agda

In Emacs/VSCode with Agda mode:
  C-c C-l  (load file)

Expected output: "Checking Hello (...)" with no errors
-}

