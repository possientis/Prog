module bin where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_;_∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_) -- \.-


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
from (n O) = 2 * (from n)
from (n I) = 2 * (from n) + 1

from-inc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
from-inc ⟨⟩ = refl
from-inc (b O) =
  begin
    from (inc (b O))
    ≡⟨⟩
    from (b I)
    ≡⟨⟩
    2 * (from b) + 1
    ≡⟨⟩
    {!!}
from-inc (b I) = {!!}





