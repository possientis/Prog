module DeBruijn.Subst where

open import Lam.Type
open import DeBruijn.Syntax
open import DeBruijn.Context

exts : ∀ {Γ Δ : Context}
  →  (∀ {A : Type} → Γ ∋ A → Δ ⊢ A)
  →  (∀ {A B : Type} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z = ` Z
exts σ (S p) = rename S_ (σ p)

subst : ∀ {Γ Δ : Context}
  →  (∀ {A : Type} → Γ ∋ A → Δ ⊢ A)
     ------------------------------
  →  (∀ {A : Type} → Γ ⊢ A → Δ ⊢ A)

subst σ (` x) = σ x
subst σ (ƛ N) = ƛ subst (exts σ) N
subst σ (L · M) = subst σ L · subst σ M
subst σ `zero = `zero
subst σ (`suc M) = `suc subst σ M
subst σ (case M M₁ M₂) = case (subst σ M) (subst σ M₁) (subst (exts σ) M₂)
subst σ (eIf M M₁ M₂) = eIf (subst σ M) (subst σ M₁) (subst σ M₂)
subst σ (μ M) = μ subst (exts σ) M
subst σ (eNum x) = eNum x
subst σ (`+ M₁ M₂) = `+ (subst σ M₁) (subst σ M₂)
subst σ (`* M₁ M₂) = `* (subst σ M₁) (subst σ M₂)
subst σ (eBool b) = eBool b
subst σ (`= M₁ M₂) = `= (subst σ M₁) (subst σ M₂)
subst σ (`< M₁ M₂) = `< (subst σ M₁) (subst σ M₂)
subst σ (`∧ M₁ M₂) = `∧ (subst σ M₁) (subst σ M₂)
subst σ (`∨ M₁ M₂) = `∨ (subst σ M₁) (subst σ M₂)

_[_] : ∀ {Γ : Context} {A B : Type}
  → Γ , B ⊢ A
  → Γ ⊢ B
    --------------------------------
  → Γ ⊢ A

_[_] {Γ} {A} {B} M N = subst σ M
  where
    σ : ∀ {C : Type} → Γ , B ∋ C → Γ ⊢ C
    σ Z = N
    σ (S x) = ` x



