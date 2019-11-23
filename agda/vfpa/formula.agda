
open import nat
open import list

-- PPIL : Positive Propositional Intuitionistic Logic
data Formula : Set where
  Var   : ℕ → Formula
  ⊤     : Formula -- \top
  _~>_  : Formula -> Formula -> Formula
  _&_   : Formula -> Formula -> Formula


Context : Set
Context = 𝕃 Formula

data _⊢_ : Context -> Formula -> Set where   -- \vdash
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

L₁ : ∀ φ Γ → Γ ⊢ φ ~> φ & φ
L₁ φ Γ = ImpI (AndI Assume Assume)

L₂ : ∀ φ ψ Γ → Γ ⊢ φ & ψ ~> ψ & φ
L₂ φ ψ Γ = ImpI (AndI (AndE2 Assume) (AndE1 Assume))

L₃ : ∀ φ ψ χ Γ → Γ ⊢ (φ & ψ) & χ ~> φ & (ψ & χ)
L₃ φ ψ χ Γ = ImpI
  (AndI (AndE1 (AndE1 Assume))
  (AndI (AndE2 (AndE1 Assume)) (AndE2 Assume)))

deduction : ∀ {φ ψ Γ} → Γ ⊢ ψ ~> φ → ψ ∷ Γ ⊢ φ
deduction p = ImpE (Weaken p) Assume

And1 : ∀ {φ ψ χ Γ} → Γ ⊢ ψ ~> φ ~> χ → Γ ⊢ (ψ & φ) ~> χ
And1 p = ImpI (ImpE (ImpE (Weaken p) (AndE1 Assume)) (AndE2 Assume))

And2 : ∀ {φ ψ χ Γ} → Γ ⊢ (ψ & φ) ~> χ → Γ ⊢ ψ ~> φ ~> χ
And2 p = ImpI (ImpI (ImpE (Weaken (Weaken p)) (AndI (Weaken Assume) Assume)))

And3 : ∀ {φ ψ χ Γ} → Γ ⊢ (φ & ψ) ~> χ → Γ ⊢ (ψ & φ) ~> χ
And3 p = ImpI (ImpE (Weaken p) (AndI (AndE2 Assume) (AndE1 Assume)))

L₄ : ∀ {φ ψ χ Γ} → φ ∷ ψ ∷ Γ ⊢ χ → ψ ∷ φ ∷ Γ ⊢ χ
L₄ p = deduction (deduction (And2 (And3 (And1 (ImpI (ImpI p))))))
