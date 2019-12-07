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


⊨-mono-ctxt : ∀ {k : Kripke} {w₁ w₂ : W k} {Γ : Context} →
  R k w₁ w₂ → k , w₁ ⊨ctxt Γ → k , w₂ ⊨ctxt Γ
⊨-mono-ctxt {k} {w₁} {w₂} {[]} p q = q
⊨-mono-ctxt {k} {w₁} {w₂} {φ ∷ Γ} p (q₁ , q₂) =
  (⊨-mono {k} {w₁} {w₂} {φ} p q₁ , ⊨-mono-ctxt p q₂)

-- Γ 'semantically entails' φ if and only if for every possible Kripke structure k
-- and every possible world w of k, if Γ is true in w then φ is true in w.
_⊨_ : Context → Formula → Set ℓ₁
Γ ⊨ φ = ∀ {k : Kripke} { w : W k} → k , w ⊨ctxt Γ → k , w ⊨ φ


sem-modus : ∀ {k : Kripke} {w : W k} {φ ψ : Formula} →
  k , w ⊨ (ψ ~> φ) → k , w ⊨ ψ → k , w ⊨ φ
sem-modus {k} {w} {φ} {ψ} p q = p (refl k w) q

-- if a formula φ is provable in a context Γ, then Γ semantically entails φ.
Soundness : ∀ {Γ : Context} {φ : Formula} → Γ ⊢ φ → Γ ⊨ φ
Soundness Assume (p , q) = p
Soundness (Weaken p) (q , r) = Soundness p r
Soundness TrueI _ = triv
Soundness (AndI p q) r = (Soundness p r , Soundness q r)
Soundness (AndE1 p) q = fst (Soundness p q)
Soundness (AndE2 p) q = snd (Soundness p q)
Soundness (ImpI p) q r s = Soundness p ( s , ⊨-mono-ctxt r q)
Soundness (ImpE p q) r = sem-modus (Soundness p r) (Soundness q r)



