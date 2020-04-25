module bin where

import Relation.Binary.PropositionalEquality.Core as Eq
open Eq              using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning  using (begin_; _≡⟨⟩_; step-≡;_∎)        -- \qed
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

-- binary addition
_⊕_ : Bin → Bin → Bin
⟨⟩ ⊕ b = b
(b O) ⊕ ⟨⟩ = b O
(b₁ O) ⊕ (b₂ O) = (b₁ ⊕ b₂) O
(b₁ O) ⊕ (b₂ I) = (b₁ ⊕ b₂) I
(b I) ⊕ ⟨⟩ = b I
(b₁ I) ⊕ (b₂ O) = (b₁ ⊕ b₂) I
(b₁ I) ⊕ (b₂ I) = inc (b₁ ⊕ b₂) O

-- binary addition is sound
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
    ≡⟨ cong (2 *_) (⊕-from m n) ⟩
    2 * (from m + from n)
    ≡⟨ *-distrib-l-+ 2 (from m) (from n) ⟩
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
    ≡⟨ cong (λ p → suc (2 * p)) (⊕-from m n) ⟩
    suc (2 * (from m + from n))
    ≡⟨ cong suc (*-distrib-l-+ 2 (from m) (from n)) ⟩
    suc (2 * from m + 2 * from n )
    ≡⟨ sym (+-suc (2 * from m) (2 * from n)) ⟩
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
    ≡⟨ cong (λ p → suc (2 * p)) (⊕-from m n) ⟩
    suc (2 * (from m + from n))
    ≡⟨ cong suc (*-distrib-l-+ 2 (from m) (from n)) ⟩
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
    ≡⟨ cong (2 *_) (from-inc (m ⊕ n)) ⟩
    2 * suc (from (m ⊕ n))
    ≡⟨ cong (λ p → 2 * suc p) (⊕-from m n) ⟩
    2 * suc (from m + from n)
    ≡⟨ suc-suc-2 _ ⟩
    suc (suc (2 * (from m + from n)))
    ≡⟨ cong (λ p → suc (suc p)) (*-distrib-l-+ 2 (from m) (from n)) ⟩
    suc (suc (2 * from m + 2 * from n))
    ≡⟨ sym (cong suc (+-suc _ _))⟩
    suc (2 * from m + suc (2 * from n))
    ≡⟨⟩
    suc (2 * from m) + suc (2 * from n)
    ≡⟨⟩
    from (m I) + from (n I)
    ∎

⊕-identity-l-inc : ∀ (n : Bin) → (⟨⟩ O) ⊕ inc n ≡ inc n
⊕-identity-l-inc ⟨⟩ = refl
⊕-identity-l-inc (n O) = refl
⊕-identity-l-inc (n I) = refl

⊕-inc-l : ∀ (m n : Bin) → inc m ⊕ n ≡ inc (m ⊕ n)
⊕-inc-l ⟨⟩ ⟨⟩ = refl
⊕-inc-l ⟨⟩ (n O) = refl
⊕-inc-l ⟨⟩ (n I) = refl
⊕-inc-l (m O) ⟨⟩ = refl
⊕-inc-l (m O) (n O) = refl
⊕-inc-l (m O) (n I) = refl
⊕-inc-l (m I) ⟨⟩ = refl
⊕-inc-l (m I) (n O) =
  begin
    inc (m I) ⊕ (n O)
    ≡⟨⟩
    (inc m O) ⊕ (n O)
    ≡⟨⟩
    (inc m ⊕ n) O
    ≡⟨ cong (λ b → b O) (⊕-inc-l m n) ⟩
    inc (m ⊕ n) O
    ≡⟨⟩
    inc ((m ⊕ n) I)
    ≡⟨⟩
    inc ((m I) ⊕ (n O))
    ∎
⊕-inc-l (m I) (n I) =
  begin
    inc (m I) ⊕ (n I)
    ≡⟨⟩
    (inc m O) ⊕ (n I)
    ≡⟨⟩
    (inc m ⊕ n) I
    ≡⟨ cong (λ b → b I) (⊕-inc-l m n) ⟩
    inc (m ⊕ n) I
    ≡⟨⟩
    inc (inc (m ⊕ n) O)
    ≡⟨⟩
    inc ((m I) ⊕ (n I))
    ∎

⊕-to : ∀ (m n : ℕ) → to m ⊕ to n ≡ to (m + n)
⊕-to zero zero = refl
⊕-to zero (suc n) = ⊕-identity-l-inc (to n)
⊕-to (suc m) n =
  begin
    to (suc m) ⊕ to n
    ≡⟨⟩
    inc (to m) ⊕ to n
    ≡⟨ ⊕-inc-l (to m) (to n) ⟩
    inc (to m ⊕ to n)
    ≡⟨ cong inc (⊕-to m n) ⟩
    inc (to (m + n))
    ≡⟨⟩
    to (suc (m + n))
    ≡⟨⟩
    to (suc m + n)
    ∎

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

⊕-b-b : ∀ {b : Bin} → One b → b ⊕ b ≡ b O
⊕-b-b justOne = refl
⊕-b-b (oneO {b} oneb) =
  begin
    (b O) ⊕ (b O)
    ≡⟨⟩
    (b ⊕ b) O
    ≡⟨ cong _O (⊕-b-b oneb) ⟩
    (b O) O
    ∎
⊕-b-b (oneI {b} oneb) =
  begin
    (b I) ⊕ (b I)
    ≡⟨⟩
    inc (b ⊕ b) O
    ≡⟨ cong (λ b → inc b O) (⊕-b-b oneb) ⟩
    inc (b O) O
    ≡⟨⟩
    (b I) O
    ∎

one-to-from justOne = refl
one-to-from (oneO {b} oneb) =
  begin
    to (from (b O))
    ≡⟨⟩
    to (2 * from b)
    ≡⟨ cong (λ n → to (from b + n)) (+-identity-r (from b)) ⟩
    to (from b + from b)
    ≡⟨ sym (⊕-to (from b) (from b)) ⟩
    to (from b) ⊕ to (from b)
    ≡⟨ cong (λ n → n ⊕ to (from b)) (one-to-from oneb) ⟩
    b ⊕ to (from b)
    ≡⟨ cong (λ n → b ⊕ n) (one-to-from oneb) ⟩
    b ⊕ b
    ≡⟨ ⊕-b-b oneb ⟩
    b O
    ∎
one-to-from (oneI {b} oneb) =
  begin
    to (from (b I))
    ≡⟨⟩
    to (suc (2 * from b))
    ≡⟨⟩
    inc (to (2 * from b))
    ≡⟨ cong (λ n → inc (to (from b + n))) (+-identity-r (from b)) ⟩
    inc (to (from b + from b))
    ≡⟨ cong inc (sym (⊕-to (from b) (from b))) ⟩
    inc (to (from b) ⊕ to (from b))
    ≡⟨ cong (λ n → inc (n ⊕ to (from b))) (one-to-from oneb) ⟩
    inc (b ⊕ to (from b))
    ≡⟨ cong (λ n → inc (b ⊕ n)) (one-to-from oneb) ⟩
    inc (b ⊕ b)
    ≡⟨ cong inc (⊕-b-b oneb) ⟩
    inc (b O)
    ≡⟨⟩
    b I
    ∎

