module sigma where

open import Agda.Primitive
open import id
open import nat
open import void

data Σ {ℓ ℓ'} (a : Set ℓ) (b : a → Set ℓ') : Set (ℓ ⊔ ℓ') where
  _,_ : (x : a) → (y : b x) → Σ a b


ℕ⁺ : Set
ℕ⁺ = Σ ℕ (λ n → ¬(n ≡ 0))


succ⁺ : ℕ⁺ → ℕ⁺
succ⁺ (n , p) = (succ n , succ-not-0 n)

_+⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
(n , p) +⁺ (m , q) = {!n + m , ?!}

