module le where

open import id
open import nat
open import sum
open import void

import min-max as min-max

data _≤_ : ℕ → ℕ → Set where
  le-n : (n : ℕ)   → n ≤ n
  le-s : {n m : ℕ} → n ≤ m → n ≤ succ m 

infixr 4 _≤_


≤-refl : (n : ℕ) → n ≤ n
≤-refl n = le-n n

≤-trans : {n m p : ℕ} → n ≤ m → m ≤ p → n ≤ p
≤-trans p (le-n n) = p
≤-trans p (le-s q) = le-s (≤-trans p q)

≤-n-s : {n m : ℕ} → n ≤ m → succ n ≤ succ m
≤-n-s (le-n n) = le-n (succ n)
≤-n-s (le-s p) = le-s (≤-n-s p)

≤-s-n : {n m : ℕ} → succ n ≤ succ m → n ≤ m
≤-s-n {n} {.n} (le-n .(succ n)) = le-n n
≤-s-n {n} {m} (le-s p)          = ≤-trans (le-s (le-n n)) p

≤-0-n : (n : ℕ) → 0 ≤ n
≤-0-n zero     = le-n 0
≤-0-n (succ n) = le-s (≤-0-n n)

≤-anti : {n m : ℕ} → n ≤ m → m ≤ n → n ≡ m
≤-anti {zero} {zero} p q     = refl _
≤-anti {succ n} {succ m} p q = ap succ (≤-anti (≤-s-n p) (≤-s-n q))

≤-s-0 : (n : ℕ) → ¬(succ n ≤ 0)
≤-s-0 n p = succ-not-0 n (≤-anti p (≤-0-n _))

≤-total : ∀ (n m : ℕ) → (n ≤ m) ∨ (m ≤ n)
≤-total zero m = left (≤-0-n m)
≤-total (succ n) zero = right (≤-0-n (succ n))
≤-total (succ n) (succ m) with ≤-total n m
≤-total (succ n) (succ m) | left  p = left (≤-n-s p)
≤-total (succ n) (succ m) | right p = right (≤-n-s p)

max : ℕ → ℕ → ℕ
max = min-max.max _≤_ ≤-refl ≤-anti ≤-total

min : ℕ → ℕ → ℕ
min = min-max.min _≤_ ≤-refl ≤-anti ≤-total

n-≤-max-n-m : (n m : ℕ) → n ≤ max n m
n-≤-max-n-m n m = min-max.x-≤-max-x-y _≤_ ≤-refl ≤-anti ≤-total n m

m-≤-max-n-m : (n m : ℕ) → m ≤ max n m
m-≤-max-n-m n m = min-max.y-≤-max-x-y _≤_ ≤-refl ≤-anti ≤-total n m
