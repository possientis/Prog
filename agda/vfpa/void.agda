module void where

data 𝕆 : Set where

¬_ : ∀ {ℓ} → Set ℓ -> Set ℓ
¬ a = a → 𝕆

infixr 70 ¬_
