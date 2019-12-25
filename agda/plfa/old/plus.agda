module plus where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import nat

_+_ : ℕ → ℕ → ℕ
zero   + m = m
succ n + m = succ (n + m)

_-_ : ℕ → ℕ → ℕ
n      - zero   = n
zero   - succ m = 0
succ n - succ m = n - m

infixl 6 _+_ _-_ -- 7 has higher precedence than 6

{-# BUILTIN NATPLUS  _+_ #-}
{-# BUILTIN NATMINUS _-_ #-}

_ : 2 + 3 ≡ 5
_ = begin
  2 + 3
  ≡⟨⟩ -- is short-hand for
  (succ (succ 0)) + (succ (succ (succ 0)))
  ≡⟨⟩ -- inductive case
  succ (succ 0 + (succ (succ (succ 0))))
  ≡⟨⟩ -- inductive case
  succ (succ (0 + (succ (succ (succ 0)))))
  ≡⟨⟩ -- base case
  succ (succ (succ (succ (succ 0))))
  ≡⟨⟩ -- is longhand for
  5
  ∎

_ : 2 + 3 ≡ 5
_ = refl

_ : 3 - 2 ≡ 1
_ = begin
  3 - 2
  ≡⟨⟩
  2 - 1
  ≡⟨⟩
  1 - 0
  ≡⟨⟩
  1 ∎

_ : 2 - 3 ≡ 0
_ = begin
  2 - 3
  ≡⟨⟩
  1 - 2
  ≡⟨⟩
  0 - 1
  ≡⟨⟩
  0 ∎
