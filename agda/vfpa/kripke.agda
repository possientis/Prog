open import nat
open import level

record Kripke : Set ℓ₁ where
  field W     : Set
  field R     : W → W → Set -- R x y : y is a possible future world of x
  field refl  : ∀ (x : W) → R x x
  field trans : ∀ {x y z : W} → R x y → R y z → R x z
  field V     : W → ℕ → Set -- V x n : n is true in world x
  field mono  : ∀ {x y : W} {n : ℕ} → R x y → V x n → V y n
