module rewrite-test where

open import nat
open import id

postulate plus-commute : (a b : ℕ) → a + b ≡ b + a
postulate P : ℕ → Set

thm : (a b : ℕ) → P (a + b) → P (b + a)
thm a b t = {!!}
