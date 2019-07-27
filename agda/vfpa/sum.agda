module sum where

open import Agda.Primitive

open import id
open import void


data _∨_ {ℓ ℓ'} (a : Set ℓ) (b : Set ℓ') : Set (ℓ ⊔ ℓ') where
  left  : (x : a) → a ∨ b
  right : (x : b) → a ∨ b

infixl 5 _∨_

eq_decidable : ∀ {ℓ} (a : Set ℓ) → Set ℓ
eq_decidable a = ∀ (x y : a) → (x ≡ y) ∨ ¬(x ≡ y)



