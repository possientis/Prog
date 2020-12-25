module DeBruijn.Syntax where

open import Data.Nat                     using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Bool                    using (Bool; true; false)
open import Relation.Nullary.Decidable   using (True; toWitness)

open import Lam.Type

open import DeBruijn.Context

infix 4 _⊢_
infix 5 ƛ_
infix 5 μ_
infixl 7 _·_  -- \cdot
infix 8 `suc_
infix 9 `_
infix 9 #_

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

  eIf : ∀ {Γ : Context} {A : Type}
    →  Γ ⊢ `𝔹
    →  Γ ⊢ A
    →  Γ ⊢ A
      ----------------------------
    →  Γ ⊢ A

  μ_ : ∀ {Γ : Context} {A : Type}
    →  Γ , A ⊢ A
      ----------------------------
    →  Γ ⊢ A

  eNum : ∀ {Γ : Context}
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

  eBool : ∀ {Γ : Context}
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

#_ : ∀ {Γ : Context}
  → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
    ---------------------------------
  → Γ ⊢ lookup (toWitness n∈Γ)

#_ n {n∈Γ} = ` count (toWitness n∈Γ)


rename : ∀ {Γ Δ : Context} {A : Type} → Γ ⊆ Δ → Γ ⊢ A → Δ ⊢ A
rename f (` p) = ` f p
rename f (ƛ p) = ƛ rename (ext f) p
rename f (p · q) = rename f p · rename f q
rename f `zero = `zero
rename f (`suc p) = `suc rename f p
rename f (case p q r) = case (rename f p) (rename f q) (rename (ext f) r)
rename f (eIf p p₁ p₂) = eIf (rename f p) (rename f p₁) (rename f p₂)
rename f (μ p) = μ rename (ext f) p
rename f (eNum x) = eNum x
rename f (`+ p q) = `+ (rename f p) (rename f q)
rename f (`* p q) = `* (rename f p) (rename f q)
rename f (eBool b) = eBool b
rename f (`= p q) = `= (rename f p) (rename f q)
rename f (`< p q) = `< (rename f p) (rename f q)
rename f (`∧ p q) = `∧ (rename f p) (rename f q)
rename f (`∨ p q) = `∨ (rename f p) (rename f q)
