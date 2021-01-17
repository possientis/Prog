module DeBruijn.Progress where


open import Data.Bool       using (Bool; true; false)
open import Lam.Type
open import DeBruijn.Value
open import DeBruijn.Syntax
open import DeBruijn.Context
open import DeBruijn.Reduction

data Progress {A : Type} (M : ∅ ⊢ A) : Set where

  step : ∀ {N : ∅ ⊢ A}
    →  M —→ N
       ---------------
    →  Progress M


  done :
       Value M
       ---------------
    →  Progress M


progress : ∀ {A : Type} (M : ∅ ⊢ A) → Progress M
progress (ƛ M) = done V-ƛ
progress (M · N) with progress M
... | step p = step (ξ-·₁ p)
... | done V-ƛ with progress N
... | step p = step (ξ-·₂ V-ƛ p)
... | done p = step (β-ƛ p)
progress `zero = done V-zero
progress (`suc M) with progress M
... | step p = step (ξ-suc p)
... | done p = done (V-suc p)
progress (case M M₁ M₂) = {!!}
progress (eIf t t₁ t₂) = {!!}
progress (μ t) = {!!}
progress (eNum x) = {!!}
progress (`+ t t₁) = {!!}
progress (`* t t₁) = {!!}
progress (eBool x) = {!!}
progress (`= t t₁) = {!!}
progress (`< t t₁) = {!!}
progress (`∧ t t₁) = {!!}
progress (`∨ t t₁) = {!!}
