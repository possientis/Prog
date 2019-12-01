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
k , w ⊨ Var n = V k w n   -- Truth specified by 'V' of Kripke structure
k , w ⊨ ⊤ = void.⊤        -- ⊤ is always true
-- The implication φ₁ ~> φ₂ is deemed true in world w, if and only if
-- for any possible future world w' or w, if φ₁ is true in w', then
-- φ₂ is also true in w'.
k , w ⊨ (φ₁ ~> φ₂) = ∀ {w' : W k} → R k w w' → k , w' ⊨ φ₁ → k , w' ⊨ φ₂
k , w ⊨ (φ₁ & φ₂) = (k , w ⊨ φ₁) ∧ (k , w ⊨ φ₂)


test : kex , w0 ⊨ (Var 0 ~> Var 1)
test rel01 v10 = v11
test rel02 v20 = v21

-- Expressing 'truth' of a context Γ in a world w of some Kripke structure k.
-- A context is deemed 'true' if and only if every one of its formula is true.
_,_⊨ctxt_ : (k : Kripke) → W k → Context → Set
k , w ⊨ctxt [] = void.⊤
k , w ⊨ctxt (φ ∷ Γ) = (k , w ⊨ φ) ∧ (k , w ⊨ctxt Γ)

-- If a formula is true in a given world, it is true in any possible future world.
⊨-mono : ∀ {k : Kripke} → {w₁ w₂ : W k} → {φ : Formula} →
  R k w₁ w₂ → k , w₁ ⊨ φ → k , w₂ ⊨ φ
⊨-mono {k} {w₁} {w₂} {Var n} p q = mono k p q
⊨-mono {k} {w₁} {w₂} {Formula.⊤} p q = q
⊨-mono {k} {w₁} {w₂} {φ₁ ~> φ₂} p q {w} r s = q (trans k p r) s
⊨-mono {k} {w₁} {w₂} {φ₁ & φ₂} p (q1 , q2) = (
  ⊨-mono {k} {w₁} {w₂} {φ₁} p q1 ,
  ⊨-mono {k} {w₁} {w₂} {φ₂} p q2 )

{-
⊨-mono-ctxt : ∀ {k : Kripke} {w₁ w₂ : W k} {Γ : Context} →
  R k w₁ w₂ → k , w₁ ⊨ctxt Γ → k , w₂ ⊨ctxt Γ
⊨-mono-ctxt {k} {w₁} {w₂} {[]} p q = q
⊨-mono-ctxt {k} {w₁} {w₂} {φ ∷ Γ} p q = {!!}
-}
