module vector where

open import bool
open import nat
open import id

-- Agda does not support overloading of functions
open import list hiding (_++_;length;map)

{- Agda supports overloading of data constructors -}
data 𝕍 {ℓ} (a : Set ℓ) : ℕ → Set ℓ where
  []  : 𝕍 a 0
  _∷_ : {n : ℕ} → a → 𝕍 a n → 𝕍 a (succ n)

infixr 5 _∷_

_++_ : ∀ {ℓ} {a : Set ℓ} {n m : ℕ} → 𝕍 a n → 𝕍 a m → 𝕍 a (n + m)
[] ++ ys       = ys
(x ∷ xs) ++ ys =  x ∷ (xs ++ ys)

test-vector1 : 𝕍 𝔹 4
test-vector1 = ff ∷ tt ∷ ff ∷ ff ∷ []

-- overloading of data constructors at play
test-vector2 : 𝕃 (𝕍 𝔹 2)
test-vector2 = (ff ∷ tt ∷ [])
             ∷ (tt ∷ ff ∷ [])
             ∷ (tt ∷ ff ∷ [])
             ∷ []

test-vector3 : 𝕍 (𝕍 𝔹 3) 2
test-vector3 = (tt ∷ tt ∷ tt ∷ [])
             ∷ (ff ∷ ff ∷ ff ∷ [])
             ∷ []

test-vector-++ : 𝕍 𝔹 8
test-vector-++ = test-vector1 ++ test-vector1

-- This function is not doing much
length : ∀ {ℓ} {a : Set ℓ} {n : ℕ} → 𝕍 a n → ℕ
length {_} {_} {n} _ = n

map : ∀ {ℓ ℓ'} {a : Set ℓ} {b : Set ℓ'} {n : ℕ} → (a → b) → 𝕍 a n -> 𝕍 b n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

head : ∀ {ℓ} {a : Set ℓ} {n : ℕ} → 𝕍 a (succ n) → a
head (x ∷ xs) = x






