open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; sym; cong)


open import Data.Nat                     using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Bool                    using (Bool; true; false)
open import Data.Empty                   using (⊥; ⊥-elim)
open import Relation.Nullary             using (Dec; yes; no; ¬_)

open import Lam.Type

open import DeBruijn.Eval
open import DeBruijn.Subst
open import DeBruijn.Value
open import DeBruijn.Syntax
open import DeBruijn.Context
open import DeBruijn.Closure
open import DeBruijn.Reduction


_ : Context
_ = ∅ , `ℕ ⇒ `ℕ , `ℕ

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ∋ `ℕ
_ = Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ∋ `ℕ ⇒ `ℕ
_ = S Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ
_ = ` Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ ⇒ `ℕ
_ = ` (S  Z)

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ
_ =  ` (S Z) · ` Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ
_ = ` S Z · (` (S Z) · ` Z)

_ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
_ = ƛ ` (S Z) · (` S Z · ` Z)

_ : ∅ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
_ = ƛ (ƛ ` S Z · (` S Z · ` Z))

_ : ∅ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
_ = ƛ ƛ # 1 · (# 1 · # 0)

two : ∀ {Γ : Context} → Γ ⊢ `ℕ
two = `suc (`suc `zero)

plus : ∀ {Γ : Context} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
plus = μ ƛ ƛ case (# 1) (# 0) (`suc (# 3 · # 0 · # 1))

2+2 : ∀ {Γ : Context} → Γ ⊢ `ℕ
2+2 = plus · two · two


Church : Type -> Type
Church A = (A ⇒ A) ⇒ A ⇒ A

twoᶜ : ∀ {Γ : Context} {A : Type} → Γ ⊢ Church A
twoᶜ = ƛ ƛ # 1 · (# 1 · # 0)

plusᶜ : ∀ {Γ : Context} {A : Type} → Γ ⊢ Church A ⇒ Church A ⇒ Church A
plusᶜ = ƛ ƛ ƛ ƛ # 3 · # 1 · (# 2 · # 1 · # 0)

sucᶜ : ∀ {Γ : Context} → Γ ⊢ `ℕ ⇒ `ℕ
sucᶜ = ƛ `suc # 0

2+2ᶜ : ∀ {Γ : Context} → Γ ⊢ `ℕ
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero

mul : ∀ {Γ : Context} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
mul = μ ƛ ƛ case (# 1) `zero (plus · # 0 · (# 3 · # 0 · # 1))

M₀ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
M₀ = ƛ # 1 · (# 1 · # 0)

M₁ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
M₁ = ƛ # 2 · (# 2 · # 0)

_ : rename S_ M₀ ≡ M₁
_ = refl

M₂ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
M₂ = ƛ # 1 · (# 1 · # 0)

M₃ : ∅ ⊢ `ℕ ⇒ `ℕ
M₃ = ƛ `suc # 0

M₄ : ∅ ⊢ `ℕ ⇒ `ℕ
M₄ = ƛ  (ƛ `suc # 0) · ( ((ƛ `suc # 0)) · # 0)

_ : M₂ [ M₃ ] ≡ M₄
_ = refl

M₅ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ
M₅ = ƛ # 0 · # 1

M₆ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ
M₆ = # 0 · `zero

M₇ : ∅ , `ℕ ⇒ `ℕ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ
M₇ = ƛ # 0 · (# 1 · `zero)

_ : M₅ [ M₆ ] ≡ M₇
_ = refl


_ : twoᶜ · sucᶜ · `zero {∅} —↠ `suc `suc `zero
_ = begin
   twoᶜ · sucᶜ · `zero
   —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
   ((ƛ # 1 · (# 1 · # 0)) [ sucᶜ ]) · `zero
   —→⟨ β-ƛ V-zero ⟩
   _
   —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
   _
   —→⟨ β-ƛ (V-suc V-zero) ⟩
   `suc `suc `zero
   ∎

{- This is taking too long: type checking hitting some exponential wall
_ : plus {∅} · two · two —↠ `suc `suc `suc `suc `zero
_ = begin
  plus · two · two
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
  _
  —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
  _
  —→⟨ β-ƛ (V-suc (V-suc (V-zero))) ⟩
  _
  —→⟨ β-suc (V-suc V-zero) ⟩
  _
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
  _
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
  _
  —→⟨ ξ-suc (β-ƛ (V-suc (V-suc (V-zero)))) ⟩
  _
  —→⟨ ξ-suc (β-suc V-zero) ⟩
  _
  —→⟨ {!!} ⟩
  {!!}
-}

sucμ : ∅ ⊢ `ℕ
sucμ = μ (`suc (# 0))

_ : eval (gas 3) sucμ ≡
  steps
    (begin
      sucμ
      —→⟨ β-μ ⟩
      `suc (μ `suc (# 0))
      —→⟨ ξ-suc β-μ ⟩
      `suc (`suc (μ `suc (# 0)))
      —→⟨ ξ-suc (ξ-suc β-μ) ⟩
      `suc (`suc (`suc (μ `suc (# 0))))
     ∎)

  out-of-gas

_ = refl

_ : eval (gas 100) (twoᶜ · sucᶜ · `zero) ≡
  steps
    (begin
      twoᶜ · sucᶜ · `zero
      —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
      _
      —→⟨ β-ƛ V-zero ⟩
      _
      —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
      _
      —→⟨ β-ƛ (V-suc V-zero) ⟩
      `suc `suc `zero
      ∎)
    (done (V-suc (V-suc V-zero)))

_ = refl

{- Too slow
_ : eval (gas 100) (plus · two · two) ≡
  steps
    (begin
      plus · two · two
      —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
      _
      —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
      _
      —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
      _
      —→⟨ β-suc (V-suc V-zero) ⟩
      _
      —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
      _
      —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
      _ —→⟨ {!!} ⟩ {!!})
    (done (V-suc (V-suc (V-suc (V-suc V-zero)))))

_ = {!!}

-}


_ : eval (gas 100) (plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero) ≡
  steps
    (begin
      plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
      —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
      _
      —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
      _
      —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
      _
      —→⟨ β-ƛ V-zero ⟩
      _
      —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
      _
      —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
      _
      —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
      _
      —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
      {!!})
    (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
_ = {!!}
