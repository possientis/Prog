module Lam.Syntax2 where

open import Data.Nat
open import Data.Bool

open import Lam.Id
open import Lam.Type
open import Lam.Context

infix 4 _⊢_


data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ : Context} {x : Id} {A : Type}
    → Γ ∋ x ∶ A
      ------------------------------------
    → Γ ⊢ A

  ƛ_ : {Γ : Context} {x : Id }{A B : Type}
    → Γ , x ∶ A ⊢ B
      ------------------------------------
    → Γ ⊢ A ⇒ B


  _·_ : ∀ {Γ : Context} {A B : Type}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ------------------------------------
    → Γ ⊢ B

  `zero : ∀ {Γ : Context}
      --------------------
    → Γ ⊢ `ℕ

  `suc_ : ∀ {Γ : Context}
    → Γ ⊢ `ℕ
      -------------------
    → Γ ⊢ `ℕ

  case : ∀ {Γ : Context} {x : Id} {A : Type}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , x ∶ `ℕ ⊢ A
      ---------------------------------------
    → Γ ⊢ A

  if : ∀ {Γ : Context} {A : Type}
    → Γ ⊢ `𝔹
    → Γ ⊢ A
    → Γ ⊢ A
      ----------------------------
    → Γ ⊢ A

  μ_ : ∀ {Γ : Context} {x : Id} {A : Type}
    → Γ , x ∶ A ⊢ A
      ----------------------------
    → Γ ⊢ A

  num : ∀ {Γ : Context}
    → ℕ
      -----------------
    → Γ ⊢ `Num


  bool : ∀ {Γ : Context}
    → Bool
      ------------------
    → Γ ⊢ `𝔹

  `+ : ∀ {Γ : Context}
    → Γ ⊢ `Num
    → Γ ⊢ `Num
      -----------------
    → Γ ⊢ `Num

  `* : ∀ {Γ : Context}
    → Γ ⊢ `Num
    → Γ ⊢ `Num
      -----------------
    → Γ ⊢ `Num

  `= : ∀ {Γ : Context}
    → Γ ⊢ `Num
    → Γ ⊢ `Num
      -----------------
    → Γ ⊢ `𝔹

  `< : ∀ {Γ : Context}
    → Γ ⊢ `Num
    → Γ ⊢ `Num
      -----------------
    → Γ ⊢ `𝔹

  `∧ : ∀ {Γ : Context}
    → Γ ⊢ `𝔹
    → Γ ⊢ `𝔹
      ----------------
    → Γ ⊢ `𝔹

  `∨ : ∀ {Γ : Context}
    → Γ ⊢ `𝔹
    → Γ ⊢ `𝔹
      ----------------
    → Γ ⊢ `𝔹
