module DeBruijn.Reduction where

open import Lam.Type
open import DeBruijn.Syntax
open import DeBruijn.Context

infix 2 _—→_ -- \em\to

data _—→_ : ∀ {Γ : Context} {A : Type} → Γ ⊢ A → Γ ⊢ A → Set where


