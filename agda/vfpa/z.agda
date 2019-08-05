module z where

import nat
open import bool
open import void

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

{-
_+_ : ℤ → ℤ → ℤ
mkℤ nat.zero _ + m = m
n + mkℤ nat.zero _ = n
mkℤ (nat.succ n) tt + mkℤ (nat.succ m) tt = mkℤ (succ n nat.+ succ m) tt
mkℤ (nat.succ n) tt + mkℤ (nat.succ m) ff = {!!}
mkℤ (nat.succ n) ff + mkℤ (nat.succ m) tt = {!!}
mkℤ (nat.succ n) ff + mkℤ (nat.succ m) ff = mkℤ (succ n nat.+ succ m) ff

diffℤ : ℕ → ℕ → ℤ
diffℤ n m = {!!}
-}
