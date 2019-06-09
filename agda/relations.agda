module relations {ℓ ℓ'} {a : Set ℓ} (_≤_ : a → a → Set ℓ') where

open import Agda.Primitive

reflexive : Set (ℓ ⊔ ℓ')
reflexive = ∀ (x : a) → x ≤ x

transitive : Set (ℓ ⊔ ℓ')
transitive = ∀ {x y z : a} → x ≤ y → y ≤ z → x ≤ z
