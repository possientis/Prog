module relations {ℓ ℓ'} {a : Set ℓ} (_≤_ : a → a → Set ℓ') where

open import Agda.Primitive

open import id
open import sum
open import void

reflexive : Set (ℓ ⊔ ℓ')
reflexive = ∀ (x : a) → x ≤ x

transitive : Set (ℓ ⊔ ℓ')
transitive = ∀ {x y z : a} → x ≤ y → y ≤ z → x ≤ z

antisymmetric : Set (ℓ ⊔ ℓ')
antisymmetric = ∀ {x y : a} → x ≤ y → y ≤ x → x ≡ y

total : Set (ℓ ⊔ ℓ')
total = ∀ (x y : a) → (x ≤ y) ∨ (y ≤ x)

decidable : Set (ℓ ⊔ ℓ')
decidable = ∀ (x y : a) → (x ≤ y) ∨ ¬(x ≤ y)

