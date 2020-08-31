module Lam.Closure  where


open import Lam.Syntax
open import Lam.Reduction

infix 2 _—↠_ -- \em\rr-
infix 1 begin_
infixr 2 _—→⟨_⟩_
infixr 2 _—→⟨⟩_
infix 3 _∎

-- reflexive and transitive closure of _—→_
data _—↠_ : Term → Term → Set where

  _∎ : ∀ (M : Term)
      ---------------
    → M —↠ M

  _—→⟨_⟩_ : ∀ (L : Term) {M N : Term}
    → L —→ M
    → M —↠ N
      ---------------
    → L —↠ N

_—→⟨⟩_ : ∀ (L : Term) {M : Term}
  → L —↠ M
    ----------
  → L —↠ M

L —→⟨⟩ p = p

begin_ : ∀ {M N : Term}
  → M —↠ N
    ----------
  → M —↠ N
begin M—↠N = M—↠N


