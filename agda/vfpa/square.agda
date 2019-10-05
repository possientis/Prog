module square where

open import id
open import nat
open import mult

data ⊥ : Set where

data Square : ℕ → Set where
  sq : (m : ℕ) → Square (m * m)

root : (n : ℕ) → Square n → ℕ
root .(m * m) (sq m) = m 

root' : (n : ℕ) → Square n → ℕ
root' _ (sq m) = m

data Even : ℕ → Set where
  even-zero  : Even 0
  even-plus2 : {n : ℕ} → Even n → Even (succ (succ n))

one-not-even : Even 1 → ⊥
one-not-even () -- if lhs contains an 'absurd' pattern, then rhs must be omitted.


max : ℕ → ℕ → ℕ
max zero m            = m
max (succ n) zero     = succ n
max (succ n) (succ m) = succ (max n m)

max-0-m : (m : ℕ) → max 0 m ≡ m
max-0-m m = refl m

max-n-0 : (n : ℕ) → max n 0 ≡ n
max-n-0 zero     = refl 0
max-n-0 (succ n) = refl (succ n)
