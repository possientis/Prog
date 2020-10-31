module Lam.Preservation where

open import Data.Nat

open import Lam.Op
open import Lam.Prim
open import Lam.Type
open import Lam.Subst
open import Lam.Value
open import Lam.Typing
open import Lam.Syntax
open import Lam.Closure
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
preserve (⊢suc p) (ξ-suc q) = ⊢suc (preserve p q)
preserve (⊢case p p₁ p₂) (ξ-case q) = ⊢case (preserve p q) p₁ p₂
preserve (⊢case p p₁ p₂) β-zero = p₁
preserve (⊢case (⊢suc p) p₁ p₂) (β-suc q) = substitution p p₂
preserve (⊢if p p₁ p₂) (ξ-if₀ q) = ⊢if (preserve p q) p₁ p₂
preserve (⊢if p p₁ p₂) β-if₁ = p₁
preserve (⊢if p p₁ p₂) β-if₂ = p₂
preserve (⊢μ p) β-μ = substitution (⊢μ p) p
preserve (⊢+ p q) (ξ-op₁ r) = ⊢+ (preserve p r) q
preserve (⊢+ p q) (ξ-op₂ r s) = ⊢+ p (preserve q s)
preserve (⊢+ p q) β-+ = ⊢Num
preserve (⊢* p q) (ξ-op₁ r) = ⊢* (preserve p r) q
preserve (⊢* p q) (ξ-op₂ r s) = ⊢* p (preserve q s)
preserve (⊢* p q) β-* = ⊢Num
preserve (⊢= p q) (ξ-op₁ r) = ⊢= (preserve p r) q
preserve (⊢= p q) (ξ-op₂ r s) = ⊢= p (preserve q s)
preserve (⊢= p q) β-= = ⊢Bool
preserve (⊢< p q) (ξ-op₁ r) = ⊢< (preserve p r) q
preserve (⊢< p q) (ξ-op₂ r s) = ⊢< p (preserve q s)
preserve (⊢< p q) β-< = ⊢Bool
preserve (⊢∧ p q) (ξ-op₁ r) = ⊢∧ (preserve p r) q
preserve (⊢∧ p q) (ξ-op₂ r s) = ⊢∧ p (preserve q s)
preserve (⊢∧ p q) β-∧ = ⊢Bool
preserve (⊢∨ p q) (ξ-op₁ r) = ⊢∨ (preserve p r) q
preserve (⊢∨ p q) (ξ-op₂ r s) = ⊢∨ p (preserve q s)
preserve (⊢∨ p q) β-∨ = ⊢Bool

preserves : ∀ {M N : Term} {A : Type}
  → ∅ ⊢ M ∶ A
  → M —↠ N  -- \em\rr-
    ----------
  → ∅ ⊢ N ∶ A

preserves p (_ ∎) = p
preserves p (_ —→⟨ q ⟩ r) = preserves (preserve p q) r
