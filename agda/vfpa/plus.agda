module plus where

open import id
open import nat

_+_ : ℕ → ℕ → ℕ
zero   + y = y
succ x + y = succ (x + y)

+-n+O : (n : ℕ)→ n + 0 ≡ n
+-n+O zero     = refl 0
+-n+O (succ n) = ap succ (+-n+O n)

+-assoc : (n m p : ℕ) → (n + m) + p ≡ n + (m + p)
+-assoc zero m p     = refl (m + p)
+-assoc (succ n) m p = ap succ (+-assoc n m p)

+-n+succ : (n m : ℕ) → n + succ m ≡ succ (n + m)
+-n+succ zero m     = refl (succ m)
+-n+succ (succ n) m = ap succ (+-n+succ n m)

+-comm : (n m : ℕ) → n + m ≡ m + n
+-comm zero m     = ≡-sym (+-n+O m)
+-comm (succ n) m = ≡-trans (ap succ (+-comm n m)) (≡-sym (+-n+succ m n))

infix 5 _+_

