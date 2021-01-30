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
progress (case M M₁ M₂) with progress M
... | step p = step (ξ-case p)
progress (case `zero M₁ M₂)    | done p = step β-zero
progress (case (`suc M) M₁ M₂) | done (V-suc p) = step (β-suc p)
progress (eIf M M₁ M₂) with progress M
... | step p = step (ξ-if₀ p)
progress (eIf (eBool false) M₁ M₂) | done p = step β-if₂
progress (eIf (eBool true) M₁ M₂) | done p = step β-if₁
progress (μ M) = step β-μ
progress (eNum n) = done V-Num
progress (eBool b)  = done V-Bool
progress (`+ M₁ M₂) with progress M₁
... | step p = step (ξ-+₁ p)
... | done V-Num with progress M₂
... | step p = step (ξ-+₂ V-Num p)
... | done V-Num = step β-+
progress (`* M₁ M₂) with progress M₁
... | step p = step (ξ-*₁ p)
... | done V-Num with progress M₂
... | step p = step (ξ-*₂ V-Num p)
... | done V-Num = step β-*
progress (`= M₁ M₂) with progress M₁
... | step p = step (ξ-=₁ p)
... | done V-Num with progress M₂
... | step p = step (ξ-=₂ V-Num p)
... | done V-Num = step β-=
progress (`< M₁ M₂) with progress M₁
... | step p = step (ξ-<₁ p)
... | done V-Num with progress M₂
... | step p = step (ξ-<₂ V-Num p)
... | done V-Num = step β-<
progress (`∧ M₁ M₂) with progress M₁
... | step p = step (ξ-∧₁ p)
... | done V-Bool with progress M₂
... | step p = step (ξ-∧₂ V-Bool p)
... | done V-Bool = step β-∧
progress (`∨ M₁ M₂) with progress M₁
... | step p = step (ξ-∨₁ p)
... | done V-Bool with progress M₂
... | step p = step (ξ-∨₂ V-Bool p)
... | done V-Bool = step β-∨
