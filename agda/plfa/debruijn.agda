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


