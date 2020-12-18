module DeBruijn.Value where

open import Data.Nat           using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Bool          using (Bool; true; false)

open import Lam.Type
open import DeBruijn.Syntax
open import DeBruijn.Context

data Value : ∀ {Γ : Context} {A : Type} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Γ : Context} {A B : Type} {N : Γ , A ⊢ B}
       ---------------------------------------------
    →  Value (ƛ N)

  V-zero : ∀ {Γ : Context}
       -------------------
    →  Value (`zero {Γ})

  V-suc : ∀ {Γ : Context} {V : Γ ⊢ `ℕ}
    →  Value V
       -------------------------------
    →  Value (`suc V)

  V-Num : ∀ {Γ : Context} {n : ℕ}
       ---------------------------
    →  Value (eNum {Γ} n)

  V-Bool : ∀ {Γ : Context} {b : Bool}
       -------------------------------
    →  Value (eBool {Γ} b)
