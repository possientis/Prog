module bin where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_;_∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_) -- \.-

open import induction

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

b₁ : Bin
b₁ = ⟨⟩ I O I I -- 11

b₂ : Bin
b₂ = ⟨⟩ O I O I I -- also 11

inc : Bin → Bin
inc ⟨⟩    = ⟨⟩ I
inc (n O) = n I
inc (n I) = inc n O

b3 : Bin
b3 = inc b₁

b4 : Bin
b4 = inc b₂

to : ℕ → Bin
to  zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩    = 0
from (b O) = 2 * (from b)
from (b I) = suc (2 * (from b))

from-inc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
from-inc ⟨⟩ = refl
from-inc (b O) =
  begin
    from (inc (b O))
    ≡⟨⟩
    from (b I)
    ≡⟨⟩
    suc (2 * (from b))
    ≡⟨⟩
    suc (from (b O))
    ∎
from-inc (b I) =
  begin
    from (inc (b I))
    ≡⟨⟩
    from (inc b O)
    ≡⟨⟩
    2 * (from (inc b))
    ≡⟨ cong (2 *_) (from-inc b) ⟩
    2 * (suc (from b))
    ≡⟨⟩
    suc (from b) + 1 * (suc (from b))
    ≡⟨⟩
    suc (from b + 1 * (suc (from b)))
    ≡⟨⟩
    suc (from b + (suc (from b) + zero))
    ≡⟨ cong (λ k → suc (from b + k)) (+-identity-r (suc (from b))) ⟩
    suc (from b + suc (from b))
    ≡⟨ cong suc (+-suc (from b) (from b)) ⟩
    suc (suc (from b + from b))
    ≡⟨ sym (cong (λ k → suc (suc (from b + k))) (+-identity-r (from b))) ⟩
    suc (suc (from b + (from b + zero)))
    ≡⟨⟩
    suc (suc (2 * from b))
    ≡⟨⟩
    suc (from (b I))
    ∎

n0 : ℕ
n0 = from ⟨⟩

n1 : ℕ
n1 = from (⟨⟩ O)


{-
-- not true: to (from ⟨⟩) = ⟨⟩ O ≠ ⟨⟩ , but both ⟨⟩ O and ⟨⟩ represent 0.
to-from : ∀ (b : Bin) → to (from b) ≡ b
to-from ⟨⟩ = {!!}
to-from (b O) = {!!}
to-from (b I) = {!!}
-}

