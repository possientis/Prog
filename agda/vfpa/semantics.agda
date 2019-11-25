open import nat
open import void
open import prod
open import list
open import level
open import kripke
open import formula

open Kripke

-- Expressing 'truth' of a formula in a world w of some Kripke structure k
_,_⊨_ : (k : Kripke) → W k → Formula → Set  -- \vDash
k , w ⊨ Var n = V k w n
k , w ⊨ ⊤ = void.⊤
k , w ⊨ (φ₁ ~> φ₂) = ∀ {w' : W k} → R k w w' → k , w' ⊨ φ₁ → k , w' ⊨ φ₂
k , w ⊨ (φ₁ & φ₂) = (k , w ⊨ φ₁) ∧ (k , w ⊨ φ₂)


test : kex , w0 ⊨ (Var 0 ~> Var 1)
test rel01 v10 = v11
test rel02 v20 = v21

_,_⊨ctxt_ : (k : Kripke) → W k → Context → Set
k , w ⊨ctxt [] = void.⊤
k , w ⊨ctxt (φ ∷ Γ) = (k , w ⊨ φ) ∧ (k , w ⊨ctxt Γ)

⊨-mono : ∀ {k : Kripke} → {w₁ w₂ : W k} → {φ : Formula} →
  R k w₁ w₂ → k , w₁ ⊨ φ → k , w₂ ⊨ φ
⊨-mono {k} {w₁} {w₂} {Var n} p q = mono k p q
⊨-mono {k} {w₁} {w₂} {Formula.⊤} p q = q
⊨-mono {k} {w₁} {w₂} {φ₁ ~> φ₂} p q {w} r s = q {w} {!!} {!!} 
⊨-mono {k} {w₁} {w₂} {x & x₁} p q = {!!}
