module bin where

open import nat
open import plus
open import mult

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
to (succ n) = inc (to n)

from : Bin → ℕ
from ⟨⟩    = 0
from (n O) = 2 * (from n)
from (n I) = 2 * (from n) + 1





