module rewrite-test where

open import id
open import nat
open import plus

postulate plus-commute : (a b : ℕ) → a + b ≡ b + a
postulate P : ℕ → Set

thm : (a b : ℕ) → P (a + b) → P (b + a)
thm a b t  with  a + b | plus-commute a b
thm a b t | .(b + a) | refl .(b + a) = t 

thm2 : (a b : ℕ) → P (a + b) → P (b + a)
thm2 a b t rewrite plus-commute a b = t






