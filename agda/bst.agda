open import relations using (transitive)

module bst {ℓ ℓ'} {a : Set ℓ}
  (_≤_ : a → a → Set ℓ')
  (≤-trans : transitive _≤_) where

