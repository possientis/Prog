module sum where

open import id
open import void

data _+_ {ℓ} : Set ℓ → Set ℓ -> Set ℓ where
  left  : {a b : Set ℓ} → (x : a) → a + b
  right : {a b : Set ℓ} → (x : b) → a + b

infixl 5 _+_

eq_decidable : ∀ {ℓ} (a : Set ℓ) → Set ℓ
eq_decidable a = ∀ (x y : a) → (x ≡ y) + ¬(x ≡ y)

