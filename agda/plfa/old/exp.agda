module exp where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import nat
open import mult

_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ succ m = n * (n ^ m)

_ : 3 ^ 4 ≡ 81
_ = begin
  3 ^ 4
  ≡⟨⟩
  3 * (3 ^ 3)
  ≡⟨⟩
  3 * (3 * (3 ^ 2))
  ≡⟨⟩
  3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
  3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
  3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩
  81 ∎
