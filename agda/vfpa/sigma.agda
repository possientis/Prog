module sigma where

open import Agda.Primitive
open import id
open import nat
open import void
open import list
open import vector

data Σ {ℓ ℓ'} (a : Set ℓ) (b : a → Set ℓ') : Set (ℓ ⊔ ℓ') where
  _,_ : (x : a) → (y : b x) → Σ a b


sum-not-0 : {n m : ℕ} → ¬(n ≡ 0) → ¬(m ≡ 0) → ¬(n + m ≡ 0)
sum-not-0 {zero}   {m} p q = q
sum-not-0 {succ n} {m} p q = succ-not-0 (n + m)

ℕ⁺ : Set
ℕ⁺ = Σ ℕ (λ n → ¬(n ≡ 0))

succ⁺ : ℕ⁺ → ℕ⁺
succ⁺ (n , p) = (succ n , succ-not-0 n)

_+⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
(n , p) +⁺ (m , q) = ((n + m) , sum-not-0 p q) 

-- returns the size of a list together with its associated vector
𝕃-to-𝕍 : ∀ {ℓ} {a : Set ℓ}  → 𝕃 a → Σ ℕ (λ n → 𝕍 a n) 
𝕃-to-𝕍 []                  = (0 , [])
𝕃-to-𝕍 (x ∷ xs) with 𝕃-to-𝕍 xs
𝕃-to-𝕍 (x ∷ xs) | (n , vs) = (succ n , (x ∷ vs))
