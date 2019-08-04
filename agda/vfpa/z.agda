module z where

open import nat
open import bool
open import void

ℤ-pos-t : ℕ → Set
ℤ-pos-t zero     = ⊤
ℤ-pos-t (succ _) = 𝔹

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


