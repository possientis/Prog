open import relations

module bst {ℓ ℓ'} {a : Set ℓ}
  (_≤_ : a → a → Set ℓ')
  (≤-trans : transitive _≤_)
  (≤-total : total _≤_)
  (≡-decidable : decidable _≡_)
  where

open import Agda.Primitive

data bst : a → a → Set (ℓ ⊔ ℓ') where
  bst-leaf : ∀ {l u : a} → l ≤ u → bst l u
  bst-node : ∀ {l l' u u' : a}
    (d : a) → bst l' d → bst d u' → l ≤ l' → u' ≤ u → bst u l


