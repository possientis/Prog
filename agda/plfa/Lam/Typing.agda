module Lam.Typing where

open import Data.Nat
open import Data.Bool

open import Lam.Id
open import Lam.Op
open import Lam.Type
open import Lam.Syntax
open import Lam.Context

infix 4 _⊢_∶_ -- \vdash for ⊢ and \: for ∶

data _⊢_∶_ : Context → Term → Type → Set where

  -- Axiom
  ⊢` : ∀ {Γ : Context} {x : Id} {A : Type}
    → Γ ∋ x ∶ A
      --------------------
    → Γ ⊢ ` x ∶ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ : Context} {x : Id} {N : Term} {A B : Type}
    → Γ , x ∶ A ⊢ N ∶ B
      --------------------
    → Γ ⊢ ƛ x ⇒ N ∶ A ⇒ B

  -- ⇒-E
  ⊢· : ∀ {Γ : Context} {L M : Term} {A B : Type}
    → Γ ⊢ L ∶ A ⇒ B
    → Γ ⊢ M ∶ A
      --------------------
    → Γ ⊢ L · M ∶ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ : Context}
      --------------------
    → Γ ⊢ `zero ∶ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ : Context} {M : Term}
    → Γ ⊢ M ∶ `ℕ
      --------------------
    → Γ ⊢ `suc M ∶ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ : Context} {L M N : Term} {x : Id} {A : Type}
    → Γ ⊢ L ∶ `ℕ
    → Γ ⊢ M ∶ A
    → Γ , x ∶ `ℕ ⊢ N ∶ A
      --------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ∶ A

  -- 𝔹-E
  ⊢if : ∀ {Γ : Context} {L M N : Term} {A : Type}
    → Γ ⊢ L ∶ `𝔹
    → Γ ⊢ M ∶ A
    → Γ ⊢ N ∶ A
     ---------------
    → Γ ⊢ eIf L M N ∶ A

  -- μ-I
  ⊢μ : ∀ {Γ : Context} {x : Id} {M : Term} {A : Type}
    → Γ , x ∶ A ⊢ M ∶ A
      --------------------
    → Γ ⊢ μ x ⇒ M ∶ A

  -- Num-I₁
  ⊢Num : ∀ {Γ : Context} {n : ℕ}
       ---------------------
    →  Γ ⊢ (eNum n) ∶ `Num

  -- Num-I₂
  ⊢+ : ∀ {Γ : Context} {M N : Term}
    → Γ ⊢ M ∶ `Num
    → Γ ⊢ N ∶ `Num
      ---------------
    → Γ ⊢ eOp `+ M N ∶ `Num

  -- Num-I₃
  ⊢* : ∀ {Γ : Context} {M N : Term}
    → Γ ⊢ M ∶ `Num
    → Γ ⊢ N ∶ `Num
      ---------------
    → Γ ⊢ eOp `* M N ∶ `Num

  -- Bool-I₁
  ⊢Bool : ∀ {Γ : Context} {b : Bool}
        --------------------
    →  Γ ⊢ (eBool b) ∶ `𝔹

  -- Bool-I₂
  ⊢= : ∀ {Γ : Context} {M N : Term}
    → Γ ⊢ M ∶ `Num
    → Γ ⊢ N ∶ `Num
      ---------------
    → Γ ⊢ eOp `= M N ∶ `𝔹

  -- Bool-I₃
  ⊢< : ∀ {Γ : Context} {M N : Term}
    → Γ ⊢ M ∶ `Num
    → Γ ⊢ N ∶ `Num
      ---------------
    → Γ ⊢ eOp `< M N ∶ `𝔹

  -- Bool-I₄
  ⊢∧ : ∀ {Γ : Context} {M N : Term}
    → Γ ⊢ M ∶ `𝔹
    → Γ ⊢ N ∶ `𝔹
      ---------------
    → Γ ⊢ eOp `∧ M N ∶ `𝔹

  -- Bool-I₅
  ⊢∨ : ∀ {Γ : Context} {M N : Term}
    → Γ ⊢ M ∶ `𝔹
    → Γ ⊢ N ∶ `𝔹
      ---------------
    → Γ ⊢ eOp `∨ M N ∶ `𝔹



