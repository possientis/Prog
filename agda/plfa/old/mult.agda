module mult where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import nat
open import plus

_*_ : ℕ → ℕ → ℕ
zero   * m = 0
succ n * m = m + (n * m)

infixl 7 _*_  -- 7 has higher precedence than 6

{-# BUILTIN NATTIMES _*_ #-}
_ : 2 * 3 ≡ 6
_ = begin
  2 * 3
  ≡⟨⟩
  3 + (1 * 3)
  ≡⟨⟩
  3 + (3 + (0 * 3))
  ≡⟨⟩
  3 + (3 + 0)
  ≡⟨⟩
  6
  ∎

