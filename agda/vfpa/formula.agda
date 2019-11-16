
open import nat
open import list

-- PPIL : Positive Propositional Intuitionistic Logic
data Formula : Set where
  Var   : ℕ → Formula
  ⊤     : Formula
  _~>_  : Formula -> Formula -> Formula
  _&_   : Formula -> Formula -> Formula


Context : Set
Context = 𝕃 Formula

data _⊢_ : Context -> Formula -> Set where
  Assume : {Γ : Context} → {φ : Formula} → (φ ∷ Γ) ⊢ φ
  Weaken : {Γ : Context} → {φ ψ : Formula} → Γ ⊢ φ → (ψ ∷ Γ) ⊢ φ
  TrueI  : {Γ : Context} → Γ ⊢ ⊤
  AndI   : {Γ : Context} → {φ ψ : Formula} → Γ ⊢ φ → Γ ⊢ ψ → Γ ⊢ (φ & ψ)
  AndE1  : {Γ : Context} → {φ ψ : Formula} → Γ ⊢ (φ & ψ) → Γ ⊢ φ
  AndE2  : {Γ : Context} → {φ ψ : Formula} → Γ ⊢ (φ & ψ) → Γ ⊢ ψ
  ImpI   : {Γ : Context} → {φ ψ : Formula} → (ψ ∷ Γ) ⊢ φ → Γ ⊢ (ψ ~> φ)
  ImpE   : {Γ : Context} → {φ ψ : Formula} → Γ ⊢ (ψ ~> φ) → Γ ⊢ ψ → Γ ⊢ φ
