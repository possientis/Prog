
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

infixr 1 _⊢_
infixr 2 _~>_
infixl 5 _&_

L₁ : ∀ (φ : Formula) → [] ⊢ φ ~> φ & φ
L₁ φ = ImpI (AndI Assume Assume)

L₂ : ∀ (φ ψ : Formula) → [] ⊢ φ & ψ ~> ψ & φ
L₂ φ ψ = ImpI (AndI (AndE2 Assume) (AndE1 Assume))

L₃ : ∀ (φ ψ χ : Formula) → [] ⊢ (φ & ψ) & χ ~> φ & (ψ & χ)
L₃ φ ψ χ = ImpI
  (AndI (AndE1 (AndE1 Assume))
  (AndI (AndE2 (AndE1 Assume)) (AndE2 Assume)))
