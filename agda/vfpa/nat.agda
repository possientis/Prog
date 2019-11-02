module nat where

open import id
open import void
open import sum

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

succ-not-0 : (n : ℕ) → ¬ (succ n ≡ 0)
succ-not-0 n ()

pred : (n : ℕ) → ℕ
pred zero     = 0
pred (succ n) = n

≡-s-n : {n m : ℕ} → succ n ≡ succ m → n ≡ m
≡-s-n (refl _) = refl _


eq-dec : eq-decidable ℕ
eq-dec zero zero = left (refl _)
eq-dec zero (succ m) = right (λ p → succ-not-0 m (≡-sym p))
eq-dec (succ n) zero = right (succ-not-0 n)
eq-dec (succ n) (succ m) with eq-dec n m
eq-dec (succ n) (succ m) | left  p = left (ap succ p)
eq-dec (succ n) (succ m) | right p = right λ q → p (≡-s-n q)
