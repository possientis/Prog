open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; sym; cong)


open import Data.Nat                     using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Bool                    using (Bool; true; false)
open import Data.Empty                   using (⊥; ⊥-elim)
open import Relation.Nullary             using (Dec; yes; no; ¬_)

open import Lam.Type

open import DeBruijn.Subst
open import DeBruijn.Syntax
open import DeBruijn.Context


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

