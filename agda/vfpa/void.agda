module void where

data ⊥ : Set where

¬_ : ∀ {ℓ} → Set ℓ -> Set ℓ
¬ a = a → ⊥

infixr 70 ¬_

data ⊤ : Set where
  triv : ⊤


absurd : ∀ {ℓ} {P : Set ℓ} → ⊥ → P
absurd ()
