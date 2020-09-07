module Lam.Canonical where

open import Data.Nat
open import Data.Bool

open import Lam.Id
open import Lam.Op
open import Lam.Type
open import Lam.Value
open import Lam.Typing
open import Lam.Syntax
open import Lam.Context
open import Lam.Reduction


infix 4 Canonical_∶_

data Canonical_∶_ : Term → Type → Set where

  C-ƛ : ∀ {x : Id} {A B : Type} {N : Term}
    →  ∅ , x ∶ A ⊢ N ∶ B
      --------------------
    → Canonical (ƛ x ⇒ N) ∶ A ⇒ B

  C-zero :
      ---------------------
      Canonical `zero ∶ `ℕ

  C-suc : ∀ {V : Term}
    →  Canonical V ∶ `ℕ
      --------------------
    → Canonical (`suc V) ∶ `ℕ

  C-Num : ∀ {n : ℕ}
      ---------------------
    → Canonical (eNum n) ∶ `Num

  C-Bool : ∀ {b : Bool}
      ----------------------
    → Canonical (eBool b) ∶ `𝔹
