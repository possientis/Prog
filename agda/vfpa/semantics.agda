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


-- if a formula φ is provable in a context Γ, then Γ semantically entails φ.
Soundness : ∀ {Γ : Context} {φ : Formula} → Γ ⊢ φ → Γ ⊨ φ
Soundness Assume (p , q) = p
Soundness (Weaken p) (q , r) = Soundness p r
Soundness TrueI _ = triv
Soundness (AndI p q) r = (Soundness p r , Soundness q r)
Soundness (AndE1 p) q = fst (Soundness p q)
Soundness (AndE2 p) q = snd (Soundness p q)
Soundness (ImpI p) q r s = Soundness p ( s , ⊨-mono-ctxt r q)
Soundness (ImpE p q) {k} {w} r = Soundness p r (refl k w) (Soundness q r)

data _≼_ : Context -> Context -> Set where
  ≼-refl : ∀ {Γ : Context} → Γ ≼ Γ
  ≼-cons : ∀ {Γ Γ' : Context} {φ : Formula} → Γ ≼ Γ' → Γ ≼ (φ ∷ Γ')

≼-trans : ∀ {Γ Γ' Γ'' : Context} → Γ ≼ Γ' → Γ' ≼ Γ'' → Γ ≼ Γ''
≼-trans p ≼-refl = p
≼-trans p (≼-cons q) = ≼-cons (≼-trans p q)

weaken-≼ : ∀ {Γ Γ' : Context} {φ : Formula} → Γ ≼ Γ' → Γ ⊢ φ → Γ' ⊢ φ
weaken-≼ ≼-refl q = q
weaken-≼ (≼-cons p) q = Weaken (weaken-≼ p q)

-- universal kripke structure
U : Kripke
U = record
  { W     = Context
  ; R     = _≼_
  ; refl  = λ Γ → ≼-refl {Γ}
  ; trans = ≼-trans
  ; V     = λ Γ n → Γ ⊢ (Var n)
  ; mono  = weaken-≼
  }

CompletenessU : ∀ {Γ : W U} {φ : Formula} → U , Γ ⊨ φ → Γ ⊢ φ
SoundnessU    : ∀ {Γ : W U} {φ : Formula} → Γ ⊢ φ → U , Γ ⊨ φ
CompletenessU {Γ} {Var n} p = p
CompletenessU {Γ} {Formula.⊤} p = TrueI
CompletenessU {Γ} {φ₁ ~> φ₂} p = ImpI
  (CompletenessU (p (≼-cons ≼-refl) (SoundnessU {φ₁ ∷ Γ} {φ₁} Assume)))
CompletenessU {Γ} {φ₁ & φ₂} (p₁ , p₂) = AndI
  (CompletenessU p₁)
  (CompletenessU p₂)
SoundnessU {Γ} {Var n} p = p
SoundnessU {Γ} {Formula.⊤} p = triv
SoundnessU {Γ} {φ₁ ~> φ₂} p {Γ'} q r = SoundnessU {Γ'} {φ₂} (ImpE
  (weaken-≼ q p) (CompletenessU r))
SoundnessU {Γ} {φ₁ & φ₂} p = (SoundnessU (AndE1 p) , SoundnessU (AndE2 p))

ctxt-id : ∀ {Γ : Context} → U , Γ ⊨ctxt Γ
ctxt-id {[]} = triv
ctxt-id {φ ∷ Γ} = (SoundnessU {φ ∷ Γ} {φ} Assume ,
  ⊨-mono-ctxt (≼-cons ≼-refl) (ctxt-id {Γ}))



