module bin where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_;_∎)         -- \qed
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_) -- \.-

open import induction
open import relations

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
-- However, if b is in canonical form... see below
to-from : ∀ (b : Bin) → to (from b) ≡ b
to-from ⟨⟩ = {!!}
to-from (b O) = {!!}
to-from (b I) = {!!}
-}

from-to : ∀ (n : ℕ) → from (to n) ≡ n
from-to zero = refl
from-to (suc n) =
  begin
    from (to (suc n))
    ≡⟨⟩
    from (inc (to n))
    ≡⟨ from-inc (to n) ⟩
    suc (from (to n))
    ≡⟨ cong suc (from-to n) ⟩
    suc n
    ∎


_⊕_ : Bin → Bin → Bin
⟨⟩ ⊕ b = b
(b O) ⊕ ⟨⟩ = b O
(b₁ O) ⊕ (b₂ O) = (b₁ ⊕ b₂) O
(b₁ O) ⊕ (b₂ I) = (b₁ ⊕ b₂) I
(b I) ⊕ ⟨⟩ = b I
(b₁ I) ⊕ (b₂ O) = (b₁ ⊕ b₂) I
(b₁ I) ⊕ (b₂ I) = inc (b₁ ⊕ b₂) O

⊕-from : ∀ (m n : Bin) → from (m ⊕ n) ≡ from m + from n
⊕-from ⟨⟩ n = refl
⊕-from (m O) ⟨⟩ = sym (+-identity-r _)
⊕-from (m O) (n O) =
  begin
    from ((m O) ⊕ (n O))
    ≡⟨⟩
    from ((m ⊕ n) O)
    ≡⟨⟩
    2 * from (m ⊕ n)
    ≡⟨ {!!} ⟩
    2 * (from m + from n)
    ≡⟨ {!!} ⟩
    2 * from m + 2 * from n
    ≡⟨⟩
    from (m O) + from (n O)
    ∎
⊕-from (m O) (n I) =
  begin
    from ((m O) ⊕ (n I))
    ≡⟨⟩
    from ((m ⊕ n) I)
    ≡⟨⟩
    suc (2 * from (m ⊕ n))
    ≡⟨ {!!} ⟩
    suc (2 * (from m + from n))
    ≡⟨ {!!} ⟩
    suc (2 * from m + 2 * from n )
    ≡⟨ {!!} ⟩
    2 * from m + suc (2 * from n)
    ≡⟨⟩
    from (m O) + from (n I)
    ∎
⊕-from (m I) ⟨⟩ = sym (cong suc (+-identity-r _))
⊕-from (m I) (n O) =
  begin
    from ((m I) ⊕ (n O))
    ≡⟨⟩
    from ((m ⊕ n) I)
    ≡⟨⟩
    suc (2 * from (m ⊕ n))
    ≡⟨ {!!} ⟩
    suc (2 * from m + 2 * from n)
    ≡⟨⟩
    suc (2 * from m) + 2 * from n
    ≡⟨⟩
    from (m I) + from (n O)
    ∎
⊕-from (m I) (n I) =
  begin
    from ((m I) ⊕ (n I))
    ≡⟨⟩
    from (inc (m ⊕ n) O)
    ≡⟨⟩ 
    2 * from (inc (m ⊕ n))
    ≡⟨ {!!} ⟩
    2 * suc (from (m ⊕ n))
    ≡⟨ {!!} ⟩
    2 * suc (from m + from n)
    ≡⟨⟩ {!!}


-- whether binary number has a leading '1'
data One : Bin → Set where
  justOne : One (⟨⟩ I)
  oneO : ∀ {b : Bin} → One b → One (b O)
  oneI : ∀ {b : Bin} → One b → One (b I)


-- whether binary number is in canonical form
data Can : Bin → Set where
  canZero : Can ((_O) ⟨⟩)  -- agda fails to parse '⟨⟩ O'
  canOne  : ∀ {b : Bin} → One b → Can b


can-inc : ∀ {b : Bin}
  →  Can b
     ----------
  →  Can (inc b)


one-inc : ∀ {b : Bin}
  →  One b
     ----------
  →  One (inc b)

one-inc justOne = oneO justOne
one-inc (oneO oneb) = oneI oneb
one-inc (oneI oneb) = oneO (one-inc oneb)

can-inc canZero = canOne justOne
can-inc (canOne oneb) = canOne (one-inc oneb)


can-to : ∀ (n : ℕ)
     ----------
  →  Can (to n)

can-to zero = canZero
can-to (suc n) = can-inc (can-to n)

can-to-from : ∀ {b : Bin}
  →  Can b
     ----------
  →  to (from b) ≡ b

one-to-from : ∀ {b : Bin}
  →  One b
     ----------
  →  to (from b) ≡ b

can-to-from canZero = refl
can-to-from (canOne oneb) = one-to-from oneb

one-to-from justOne = refl
one-to-from (oneO {b} oneb) =
  begin
    to (from (b O))
    ≡⟨⟩
    to (2 * from b)
    ≡⟨⟩
    {!!}
one-to-from (oneI oneb) = {!!}
