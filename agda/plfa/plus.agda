module plus where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import nat

_+_ : ℕ → ℕ → ℕ
zero   + m = m
succ n + m = succ (n + m)

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

