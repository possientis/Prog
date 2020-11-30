open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; sym; cong)


open import Data.Nat                     using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Bool                    using (Bool; true; false)
open import Data.Empty                   using (⊥; ⊥-elim)
open import Relation.Nullary             using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable   using (True; toWitness)

open import Lam.Type

infix 4 _⊢_
infix 4 _∋_
infixl 5 _,_

infix 5 ƛ_
infix 5 μ_
infixl 7 _·_  -- \cdot
infix 8 `suc_
infix 9 `_
infix 9 S_
infix 9 #_


data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

_ : Context
_ = ∅ , `ℕ ⇒ `ℕ , `ℕ

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ : Context} {A : Type}
      ------------------------------
    → Γ , A ∋ A


  S_ : ∀ {Γ : Context} {A B : Type}
    →  Γ ∋ A
       ------------------------------
    →  Γ , B ∋ A

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ∋ `ℕ
_ = Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ∋ `ℕ ⇒ `ℕ
_ = S Z


data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ : Context} {A : Type}
    →  Γ ∋ A
      ---------------------------
    →  Γ ⊢ A

  ƛ_ : ∀ {Γ : Context} {A B : Type}
    →  Γ , A ⊢ B
       ---------------------------
    →  Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ : Context} {A B : Type}
    →  Γ ⊢ A ⇒ B
    →  Γ ⊢ A
       ---------------------------
    →  Γ ⊢ B

  `zero : ∀ {Γ : Context}
       ------------------
    →   Γ ⊢ `ℕ

  `suc_ : ∀ {Γ : Context}
    →   Γ ⊢ `ℕ
       ------------------
    →   Γ ⊢ `ℕ

  case : ∀ {Γ : Context} {A : Type}
    →   Γ ⊢ `ℕ
    →   Γ ⊢ A
    →   Γ , `ℕ ⊢ A
       ----------------------------
    →   Γ ⊢ A

  if : ∀ {Γ : Context} {A : Type}
    →  Γ ⊢ `𝔹
    →  Γ ⊢ A
    →  Γ ⊢ A
      ----------------------------
    →  Γ ⊢ A

  μ_ : ∀ {Γ : Context} {A : Type}
    →  Γ , A ⊢ A
      ----------------------------
    →  Γ ⊢ A

  num : ∀ {Γ : Context}
    →  ℕ
      ------------------
    →  Γ ⊢ `Num

  `+ : ∀ {Γ : Context}
    →  Γ ⊢ `Num
    →  Γ ⊢ `Num
       -----------------
    →  Γ ⊢ `Num

  `* : ∀ {Γ : Context}
    →  Γ ⊢ `Num
    →  Γ ⊢ `Num
       -----------------
    →  Γ ⊢ `Num

  bool : ∀ {Γ : Context}
    →  Bool
       -----------------
    →  Γ ⊢ `𝔹

  `= : ∀ {Γ : Context}
    →  Γ ⊢ `Num
    →  Γ ⊢ `Num
      ------------------
    →  Γ ⊢ `𝔹

  `< : ∀ {Γ : Context}
    →  Γ ⊢ `Num
    →  Γ ⊢ `Num
      ------------------
    →  Γ ⊢ `𝔹

  `∧ : ∀ {Γ : Context}
    →  Γ ⊢ `𝔹
    →  Γ ⊢ `𝔹
      ------------------
    →  Γ ⊢ `𝔹

  `∨ : ∀ {Γ : Context}
    →  Γ ⊢ `𝔹
    →  Γ ⊢ `𝔹
      ------------------
    →  Γ ⊢ `𝔹


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


length : Context → ℕ
length ∅ = zero
length (Γ , _) = suc (length Γ)

lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
lookup {_ , A} {zero} (s≤s z≤n) = A
lookup {_ , _} {suc n} (s≤s p) = lookup p

count : ∀ {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
count {_ , _} {zero} (s≤s z≤n) = Z
count {Γ , A} {suc n} (s≤s p) = S (count p)

#_ : ∀ {Γ : Context}
  → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
    ---------------------------------
  → Γ ⊢ lookup (toWitness n∈Γ)

#_ n {n∈Γ} = ` count (toWitness n∈Γ)

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

_⊆_ : Context -> Context -> Set
_⊆_ Γ Δ = ∀ {A : Type } → Γ ∋ A → Δ ∋ A

infix 4 _⊆_

⊆-refl : ∀ {Γ : Context} → Γ ⊆ Γ
⊆-refl p = p

⊆-trans : ∀ {Γ Δ Ε : Context} → Γ ⊆ Δ → Δ ⊆ Ε → Γ ⊆ Ε
⊆-trans p q r = q (p r)

ext : ∀ {Γ Δ : Context} {A : Type}
  →   Γ ⊆ Δ
      --------------
  →   Γ , A ⊆ Δ , A

ext f Z = Z
ext f (S p) = S f p

rename : ∀ {Γ Δ : Context} {A : Type} → Γ ⊆ Δ → Γ ⊢ A → Δ ⊢ A
rename f (` p) = ` f p
rename f (ƛ p) = ƛ rename (ext f) p
rename f (p · q) = rename f p · rename f q
rename f `zero = `zero
rename f (`suc p) = `suc rename f p
rename f (case p q r) = case (rename f p) (rename f q) (rename (ext f) r)
rename f (if p p₁ p₂) = if (rename f p) (rename f p₁) (rename f p₂)
rename f (μ p) = μ rename (ext f) p
rename f (num x) = num x
rename f (`+ p q) = `+ (rename f p) (rename f q)
rename f (`* p q) = `* (rename f p) (rename f q)
rename f (bool b) = bool b
rename f (`= p q) = `= (rename f p) (rename f q)
rename f (`< p q) = `< (rename f p) (rename f q)
rename f (`∧ p q) = `∧ (rename f p) (rename f q)
rename f (`∨ p q) = `∨ (rename f p) (rename f q)


M₀ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
M₀ = ƛ # 1 · (# 1 · # 0)

M₁ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
M₁ = ƛ # 2 · (# 2 · # 0)

_ : rename S_ M₀ ≡ M₁
_ = refl



