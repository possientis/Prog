module Naturals where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)


_*_ : ℕ → ℕ → ℕ
zero * m  = zero
suc n * m = m + (n * m)

_ : 2 * 3 ≡ 6
_ =
  begin
  2 * 3
  ≡⟨⟩ 3 + (1 * 3)
  ≡⟨⟩ 3 + (3 + (0 * 3))
  ≡⟨⟩ 3 + (3 + 0)
  ≡⟨⟩ 6
  ∎
