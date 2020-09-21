module Lam.Progress where

open import Data.Bool       using (Bool; true; false)
open import Lam.Type
open import Lam.Value
open import Lam.Syntax
open import Lam.Typing
open import Lam.Context
open import Lam.Reduction

data Progress (M : Term) : Set where

  step : ∀ {N : Term}
   → M —→ N
     ----------
   → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {M : Term} {A : Type}
  → ∅ ⊢ M ∶ A
    ----------
  → Progress M

progress (⊢ƛ p) = done V-ƛ
progress (⊢· p q) with (progress p)
... | step r = step (ξ-·₁ r)
... | done r with (progress q)
... | step s = step (ξ-·₂ r s)
progress (⊢· (⊢ƛ p) q) | done r | done s = step (β-ƛ s)
progress ⊢zero = done V-zero
progress (⊢suc p) with progress p
... | step q = step (ξ-suc q)
... | done q = done (V-suc q)
progress (⊢case p q r) with progress p
... | step s = step (ξ-case s)
... | done V-zero = step β-zero
... | done (V-suc s) = step (β-suc s)
progress (⊢μ p) = step β-μ
progress ⊢Num = done V-Num
progress (⊢+ p q) with progress p
... | step r = step (ξ-op₁ r)
... | done r with progress q
... | step s = step (ξ-op₂ r s)
progress (⊢+ p q) | done V-Num | done V-Num = step β-+
progress (⊢* p q) with progress p
... | step r = step (ξ-op₁ r)
... | done r with progress q
... | step s = step (ξ-op₂ r s)
progress (⊢* p q) | done V-Num | done V-Num = step β-*
progress ⊢Bool = done V-Bool
progress (⊢= p q) with progress p
... | step r = step (ξ-op₁ r)
... | done r with progress q
... | step s = step (ξ-op₂ r s)
progress (⊢= p q) | done V-Num | done V-Num = step β-=
progress (⊢< p q) with progress p
... | step r = step (ξ-op₁ r)
... | done r with progress q
... | step s = step (ξ-op₂ r s)
progress (⊢< p q) | done V-Num | done V-Num = step β-<
progress (⊢∧ p q) with progress p
... | step r = step (ξ-op₁ r)
... | done r with progress q
... | step s = step (ξ-op₂ r s)
progress (⊢∧ p q) | done V-Bool | done V-Bool = step β-∧
progress (⊢∨ p q) with progress p
... | step r = step (ξ-op₁ r)
... | done r with progress q
... | step s = step (ξ-op₂ r s)
progress (⊢∨ p q) | done V-Bool | done V-Bool = step β-∨
progress (⊢if p q r) with progress p
... | step s = step (ξ-if₀ s)
progress (⊢if p q r) | done (V-Bool {false}) = step β-if₂
progress (⊢if p q r) | done (V-Bool {true}) = step β-if₁
