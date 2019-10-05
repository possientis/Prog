module z where

import plus
import le

open import id
open import lt
open import nat
open import bool
open import void
open import sum

ℤ-pos-t : ℕ → Set
ℤ-pos-t nat.zero     = ⊤
ℤ-pos-t (nat.succ _) = 𝔹

data ℤ : Set where
  mkℤ : (n : ℕ) → ℤ-pos-t n → ℤ 


0ℤ : ℤ
0ℤ = mkℤ 0 triv

1ℤ : ℤ
1ℤ = mkℤ 1 tt

-1ℤ : ℤ
-1ℤ = mkℤ 1 ff

abs : ℤ → ℕ
abs (mkℤ n _) = n

is-even : ℕ → 𝔹
is-odd  : ℕ → 𝔹
is-even zero     = tt
is-even (succ n) = is-odd n
is-odd zero      = ff
is-odd (succ n)  = is-even n

is-evenℤ : ℤ → 𝔹
is-evenℤ (mkℤ n _) = is-even n


is-oddℤ : ℤ → 𝔹
is-oddℤ (mkℤ n _) = is-odd n

ℕ-trichotomy : (n m : ℕ) → (n < m) ∨ (n ≡ m) ∨ (m < n)
ℕ-trichotomy zero zero      = left ( right (refl 0))
ℕ-trichotomy zero (nat.succ m)  = left (left (le.≤-n-s (le.≤-0-n m)))
ℕ-trichotomy (nat.succ n) zero  = right (le.≤-n-s (le.≤-0-n n))
ℕ-trichotomy (nat.succ n) (nat.succ m) with ℕ-trichotomy n m
ℕ-trichotomy (nat.succ n) (nat.succ m) | left (left p)  = left (left (le.≤-n-s p))
ℕ-trichotomy (nat.succ n) (nat.succ m) | left (right p) = left (right (ap nat.succ p))
ℕ-trichotomy (nat.succ n) (nat.succ m) | right p        = right (le.≤-n-s p)

-- diffℕ n m = n - m
diffℕ : {n m : ℕ} → (m le.≤ n) → ℕ
diffℕ {n} {zero} _        = n
diffℕ {nat.succ n} {nat.succ m} p = diffℕ (le.≤-s-n p)

diffℕ-pos : (n m : ℕ) -> (p : m le.≤ n) -> (q : m < n) → diffℕ p ≡ nat.succ (diffℕ q)
diffℕ-pos (nat.succ n) zero p q     = refl (nat.succ n)
diffℕ-pos (nat.succ n) (nat.succ m) p q = diffℕ-pos n m (le.≤-s-n p) (<-s-n q)


-- diffℤ n m = n - m
diffℤ : ℕ → ℕ → ℤ
diffℤ n m with ℕ-trichotomy n m
diffℤ n m | left (left p)  = mkℤ
  (diffℕ (le.≤-trans (le.le-s (le.le-n n)) p))
  (cast (ap ℤ-pos-t (≡-sym (diffℕ-pos m n _ p))) ff)
diffℤ n m | left (right p) = 0ℤ
diffℤ n m | right p        = mkℤ
  (diffℕ (le.≤-trans (le.le-s (le.le-n m)) p))
  (cast (ap ℤ-pos-t (≡-sym (diffℕ-pos n m _ p))) tt)

_+_ : ℤ → ℤ → ℤ
mkℤ nat.zero _ + m = m
n + mkℤ nat.zero _ = n
mkℤ (nat.succ n) tt + mkℤ (nat.succ m) tt = mkℤ (nat.succ n plus.+ succ m) tt
mkℤ (nat.succ n) tt + mkℤ (nat.succ m) ff = diffℤ n m
mkℤ (nat.succ n) ff + mkℤ (nat.succ m) tt = diffℤ m n
mkℤ (nat.succ n) ff + mkℤ (nat.succ m) ff = mkℤ (succ n plus.+ succ m) ff


+-n+0 : (n : ℤ) → n + 0ℤ ≡ n
+-n+0 (mkℤ nat.zero triv)   = refl _
+-n+0 (mkℤ (nat.succ n) tt) = refl _
+-n+0 (mkℤ (nat.succ n) ff) = refl _

data _≤_ : ℤ → ℤ → Set where
  le-0-0     : mkℤ 0 triv ≤ mkℤ 0 triv
  le-0-pos   : (n : ℕ) → mkℤ 0 triv ≤ mkℤ (nat.succ n) tt
  le-neg-0   : (n : ℕ) → mkℤ (nat.succ n) ff ≤ mkℤ 0 triv
  le-neg-pos : (n m : ℕ) → mkℤ (nat.succ n) ff ≤ mkℤ (nat.succ m) tt
  le-neg-neg : {n m : ℕ} → (m le.≤ n) → mkℤ (nat.succ n) ff ≤  mkℤ (nat.succ m) ff
  le-pos-pos : {n m : ℕ} → (n le.≤ m) → mkℤ (nat.succ n) tt ≤  mkℤ (nat.succ m) tt

infixr 4 _≤_

≤-refl : (n : ℤ) → n ≤ n
≤-refl (mkℤ nat.zero triv)   = le-0-0
≤-refl (mkℤ (nat.succ n) tt) = le-pos-pos (le.≤-refl n)
≤-refl (mkℤ (nat.succ n) ff) = le-neg-neg (le.≤-refl n)

≤-anti : {n m : ℤ} → n ≤ m → m ≤ n → n ≡ m
≤-anti {mkℤ nat.zero triv} {mkℤ nat.zero triv} p q = refl _
≤-anti {mkℤ nat.zero triv} {mkℤ (nat.succ m) tt} p ()
≤-anti {mkℤ nat.zero triv} {mkℤ (nat.succ m) ff} () q
≤-anti {mkℤ (nat.succ n) tt} {mkℤ nat.zero triv} () q
≤-anti {mkℤ (nat.succ n) ff} {mkℤ nat.zero triv} p ()
≤-anti {mkℤ (nat.succ n) tt} {mkℤ (nat.succ m) tt}
  (le-pos-pos p) (le-pos-pos q) = ap (λ x → mkℤ (nat.succ x) tt) (le.≤-anti p q)
≤-anti {mkℤ (nat.succ n) ff} {mkℤ (nat.succ m) ff}
  (le-neg-neg p) (le-neg-neg q) = ap (λ x → mkℤ (nat.succ x) ff) (le.≤-anti q p)

≤-trans : {n m p : ℤ} → n ≤ m → m ≤ p → n ≤ p
≤-trans {mkℤ nat.zero triv} {mkℤ nat.zero triv} {mkℤ nat.zero triv} q r = le-0-0
≤-trans {mkℤ nat.zero triv} {mkℤ nat.zero triv} {mkℤ (nat.succ p) tt} q r = le-0-pos p
≤-trans {mkℤ nat.zero triv} {mkℤ (nat.succ m) tt} {mkℤ (nat.succ p) tt} q r =
  le-0-pos p
≤-trans {mkℤ (nat.succ n) tt} {mkℤ (nat.succ m) tt} {mkℤ (nat.succ p) tt}
        (le-pos-pos q) (le-pos-pos r) = le-pos-pos (le.≤-trans q r)
≤-trans {mkℤ (nat.succ n) ff} {mkℤ nat.zero triv} {mkℤ nat.zero triv} q r =
  le-neg-0 n
≤-trans {mkℤ (nat.succ n) ff} {mkℤ nat.zero triv} {mkℤ (nat.succ p) tt} q r =
  le-neg-pos n p
≤-trans {mkℤ (nat.succ n) ff} {mkℤ (nat.succ m) tt} {mkℤ (nat.succ p) tt} q r =
  le-neg-pos n p
≤-trans {mkℤ (nat.succ n) ff} {mkℤ (nat.succ m) ff} {mkℤ nat.zero triv} q r =
  le-neg-0 n
≤-trans {mkℤ (nat.succ n) ff} {mkℤ (nat.succ m) ff} {mkℤ (nat.succ p) tt} q r =
  le-neg-pos n p
≤-trans {mkℤ (nat.succ n) ff} {mkℤ (nat.succ m) ff} {mkℤ (nat.succ p) ff}
  (le-neg-neg q) (le-neg-neg r) = le-neg-neg (le.≤-trans r q) 


{- appears to be non-trivial
+-assoc : (n m p : ℤ) → (n + m) + p ≡ n + (m + p)
+-assoc (mkℤ nat.zero triv) (mkℤ m s) (mkℤ p t) = refl _
+-assoc (mkℤ (nat.succ n) r) (mkℤ nat.zero triv) (mkℤ p t) = refl _
+-assoc (mkℤ (nat.succ n) r) (mkℤ (nat.succ m) s) (mkℤ nat.zero triv) =
  ≡-trans
    (≡-sym (ap (λ x → (mkℤ (nat.succ n) r + mkℤ (nat.succ m) s) + x) (refl 0ℤ)))
    (+-n+0 _)
+-assoc (mkℤ (nat.succ n) tt) (mkℤ (nat.succ m) tt) (mkℤ (nat.succ p) tt) =
  ap (λ x → mkℤ (nat.succ x) tt) (nat.+-assoc n (nat.succ m) (nat.succ p))
+-assoc (mkℤ (nat.succ n) tt) (mkℤ (nat.succ m) tt) (mkℤ (nat.succ p) ff) = {!!}
+-assoc (mkℤ (nat.succ n) tt) (mkℤ (nat.succ m) ff) (mkℤ (nat.succ p) t) = {!!}
+-assoc (mkℤ (nat.succ n) ff) (mkℤ (nat.succ m) s) (mkℤ (nat.succ p) t) = {!!}
-}


