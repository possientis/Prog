module prod where

open import Agda.Primitive

data _∧_ {ℓ ℓ'} (a : Set ℓ) (b : Set ℓ') : Set (ℓ ⊔ ℓ') where
  _,_ : (x : a) → (y : b) → a ∧ b
