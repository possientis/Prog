module DeBruijn.Closure where

open import Lam.Type
open import DeBruijn.Syntax
open import DeBruijn.Context

infix 2 _—↠_  -- \em\rr-
infix 1 begin_
infixr 2 _—→⟨_⟩_
infix 3 _∎    -- \qed


data _—↠_ {Γ : Context} {A : Type} : Γ ⊢ A → Γ ⊢ A → Set where

  _∎ : (M : Γ ⊢ A)
     ---------------
   → M —↠ M
