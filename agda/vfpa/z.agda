module z where

import nat
open import id
open import bool
open import void
open import sum

ℕ = nat.ℕ

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


is-evenℤ : ℤ → 𝔹
is-evenℤ (mkℤ n _) = nat.is-even n


is-oddℤ : ℤ → 𝔹
is-oddℤ (mkℤ n _) = nat.is-odd n

succ = nat.succ

-- diffℤ n m = n - m
diffℤ : ℕ → ℕ → ℤ
diffℤ n m with nat.ℕ-trichotomy n m
diffℤ n m | left (left p)  = mkℤ
  (nat.diffℕ (nat.≤-trans (nat.le-s (nat.le-n n)) p))
  (cast (ap ℤ-pos-t (≡-sym (nat.diffℕ-pos m n _ p))) ff)
diffℤ n m | left (right p) = 0ℤ
diffℤ n m | right p        = mkℤ
  (nat.diffℕ (nat.≤-trans (nat.le-s (nat.le-n m)) p))
  (cast (ap ℤ-pos-t (≡-sym (nat.diffℕ-pos n m _ p))) tt)

_+_ : ℤ → ℤ → ℤ
mkℤ nat.zero _ + m = m
n + mkℤ nat.zero _ = n
mkℤ (nat.succ n) tt + mkℤ (nat.succ m) tt = mkℤ (succ n nat.+ succ m) tt
mkℤ (nat.succ n) tt + mkℤ (nat.succ m) ff = diffℤ n m
mkℤ (nat.succ n) ff + mkℤ (nat.succ m) tt = diffℤ m n
mkℤ (nat.succ n) ff + mkℤ (nat.succ m) ff = mkℤ (succ n nat.+ succ m) ff


+-n+0 : (n : ℤ) → n + 0ℤ ≡ n
+-n+0 (mkℤ nat.zero triv)   = refl _
+-n+0 (mkℤ (nat.succ n) tt) = refl _
+-n+0 (mkℤ (nat.succ n) ff) = refl _

data _≤_ : ℤ → ℤ → Set where
  le-0-0     : mkℤ 0 triv ≤ mkℤ 0 triv
  le-0-pos   : (n : ℕ) → mkℤ 0 triv ≤ mkℤ (nat.succ n) tt
  le-neg-0   : (n : ℕ) → mkℤ (nat.succ n) ff ≤ mkℤ 0 triv
  le-neg-pos : (n m : ℕ) → mkℤ (nat.succ n) ff ≤ mkℤ (nat.succ m) tt
  le-neg-neg : {n m : ℕ} → (m nat.≤ n) → mkℤ (nat.succ n) ff ≤  mkℤ (nat.succ m) ff
  le-pos-pos : {n m : ℕ} → (n nat.≤ m) → mkℤ (nat.succ n) tt ≤  mkℤ (nat.succ m) tt

infixr 4 _≤_

≤-refl : (n : ℤ) → n ≤ n
≤-refl (mkℤ nat.zero triv)   = le-0-0
≤-refl (mkℤ (nat.succ n) tt) = le-pos-pos (nat.≤-refl n)
≤-refl (mkℤ (nat.succ n) ff) = {!le-neg-neg (nat.≤-refl n)!}


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


