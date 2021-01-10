module DeBruijn.Closure where

open import Lam.Type
open import DeBruijn.Syntax
open import DeBruijn.Context
open import DeBruijn.Reduction

infix 2 _—↠_  -- \em\rr-
infix 1 begin_
infixr 2 _—→⟨_⟩_
infix 3 _∎    -- \qed


data _—↠_ {Γ : Context} {A : Type} : Γ ⊢ A → Γ ⊢ A → Set where

  _∎ : (M : Γ ⊢ A)
     ---------------
   → M —↠ M

  _—→⟨_⟩_ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      -------------------------------
    → L —↠ N

begin_ : ∀ {Γ : Context} {A : Type} {M N : Γ ⊢ A}
  → M —↠ N
    ---------------------------------------------
  → M —↠ N
begin p = p
