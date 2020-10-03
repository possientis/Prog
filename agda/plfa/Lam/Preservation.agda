module Lam.Preservation where

open import Lam.Type
open import Lam.Subst
open import Lam.Value
open import Lam.Typing
open import Lam.Syntax
open import Lam.Context
open import Lam.Reduction
open import Lam.Substitution

preserve : ∀ {M N : Term} {A : Type}
  → ∅ ⊢ M ∶ A
  → M —→ N
    ----------
  → ∅ ⊢ N ∶ A
preserve (⊢· p q) (ξ-·₁ r) = ⊢· (preserve p r) q
preserve (⊢· p q) (ξ-·₂ r s) = ⊢· p (preserve q s)
preserve (⊢· (⊢ƛ p) q) (β-ƛ r) = substitution q p
preserve (⊢suc p) q = {!!}
preserve (⊢case p p₁ p₂) q = {!!}
preserve (⊢if p p₁ p₂) q = {!!}
preserve (⊢μ p) q = {!!}
preserve (⊢+ p p₁) q = {!!}
preserve (⊢* p p₁) q = {!!}
preserve (⊢= p p₁) q = {!!}
preserve (⊢< p p₁) q = {!!}
preserve (⊢∧ p p₁) q = {!!}
preserve (⊢∨ p p₁) q = {!!}
