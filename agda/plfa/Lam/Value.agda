module Lam.Value where

open import Data.Nat
open import Data.Bool

open import Lam.Id
open import Lam.Syntax

data Value : Term -> Set where

  V-ƛ : ∀ {x : Id} {N : Term}
      -----------------------
    → Value (ƛ x ⇒ N)

  V-zero :
      -----------------------
      Value `zero

  V-suc : ∀ {V : Term}
    → Value V
      -----------------------
    → Value (`suc V)

  V-Num : ∀ {n : ℕ }
       --------------------
    →  Value (eNum n)

  V-Bool : ∀ {b : Bool}
       -------------------
    →  Value (eBool b)

