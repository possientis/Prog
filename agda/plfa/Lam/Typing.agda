module Lam.Typing where


open import Lam.Id
open import Lam.Type
open import Lam.Syntax
open import Lam.Context

infix 4 _⊢_∶_ -- \vdash for ⊢ and \: for ∶

data _⊢_∶_ : Context → Term → Type → Set where

  -- Axiom
  ⊢` : ∀ {Γ : Context} {x : Id} {A : Type}
    → Γ ∋ x ∶ A
      --------------------
    → Γ ⊢ ` x ∶ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ : Context} {x : Id} {N : Term} {A B : Type}
    → Γ , x ∶ A ⊢ N ∶ B
      --------------------
    → Γ ⊢ ƛ x ⇒ N ∶ A ⇒ B

  -- ⇒-E
  ⊢· : ∀ {Γ : Context} {L M : Term} {A B : Type}
    → Γ ⊢ L ∶ A ⇒ B
    → Γ ⊢ M ∶ A
      --------------------
    → Γ ⊢ L · M ∶ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ : Context}
      --------------------
    → Γ ⊢ `zero ∶ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ : Context} {M : Term}
    → Γ ⊢ M ∶ `ℕ
      --------------------
    → Γ ⊢ `suc M ∶ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ : Context} {L M N : Term} {x : Id} {A : Type}
    → Γ ⊢ L ∶ `ℕ
    → Γ ⊢ M ∶ A
    → Γ , x ∶ `ℕ ⊢ N ∶ A
      --------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ∶ A

  -- μ-I
  ⊢μ : ∀ {Γ : Context} {x : Id} {M : Term} {A : Type}
    → Γ , x ∶ A ⊢ M ∶ A
      --------------------
    → Γ ⊢ μ x ⇒ M ∶ A


