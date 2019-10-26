module plus where

open import le
open import id
open import nat

_+_ : ℕ → ℕ → ℕ
zero   + y = y
succ x + y = succ (x + y)

n+0≡0 : (n : ℕ)→ n + 0 ≡ n
n+0≡0 zero     = refl 0
n+0≡0 (succ n) = ap succ (n+0≡0 n)

+-assoc : (n m p : ℕ) → (n + m) + p ≡ n + (m + p)
+-assoc zero m p     = refl (m + p)
+-assoc (succ n) m p = ap succ (+-assoc n m p)

n+sm≡sn+m : (n m : ℕ) → n + succ m ≡ succ (n + m)
n+sm≡sn+m zero m     = refl (succ m)
n+sm≡sn+m (succ n) m = ap succ (n+sm≡sn+m n m)

+-comm : (n m : ℕ) → n + m ≡ m + n
+-comm zero m     = ≡-sym (n+0≡0 m)
+-comm (succ n) m = ≡-trans (ap succ (+-comm n m)) (≡-sym (n+sm≡sn+m m n))

infix 5 _+_

n-≤-n+m : (n m : ℕ) → n ≤ n + m
n-≤-n+m zero m     = 0-≤-n _
n-≤-n+m (succ n) m = ≤-n-s (n-≤-n+m _ _)

m-≤-n+m : (n m : ℕ) → m ≤ n + m
m-≤-n+m zero m     = ≤-refl _
m-≤-n+m (succ n) m = le-s (m-≤-n+m _ _)

{-
+-≤-compat-l : {n m : ℕ} (p : ℕ) → n ≤ m → p + n ≤ p + m
+-≤-compat-l p (le-n n) = ≤-refl _
+-≤-compat-l zero (le-s q) = le-s q
+-≤-compat-l {n} {m} (succ p) (le-s q) = ≤-n-s
  (leibniz (λ x → p + n ≤ x) {!!} {!n+sm≡sn+m!})
-}
