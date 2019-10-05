module nat where

open import id
open import void

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

succ-not-0 : (n : ℕ) → ¬ (succ n ≡ 0)
succ-not-0 n ()

pred : (n : ℕ) → ℕ
pred zero     = 0
pred (succ n) = n

