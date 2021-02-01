module DeBruijn.Eval where

open import Data.Nat         using (ℕ; zero; suc)

record Gas : Set where
  constructor gas
  field
    amount : ℕ

open import Lam.Type
open import DeBruijn.Value
open import DeBruijn.Syntax
open import DeBruijn.Closure
open import DeBruijn.Context
open import DeBruijn.Progress

data Finished {Γ : Context} {A : Type} (N : Γ ⊢ A) : Set where

  done :
      Value N
    -----------
    → Finished N

  out-of-gas :
    -----------
      Finished N

data Steps {A : Type} (L : ∅ ⊢ A) : Set where

  steps : ∀ {N : ∅ ⊢ A}
    →  L —↠ N
    →  Finished N
      ------------
    →  Steps L

eval : ∀ {A : Type}
  → Gas
  → (L : ∅ ⊢ A)
    -------------
  → Steps L

eval (gas zero) L = steps (L ∎) out-of-gas
eval (gas (suc n)) L with progress L
... | done p = steps (L ∎) (done p)
... | step {N} p with eval (gas n) N
... | steps q f = steps (L —→⟨ p ⟩ q) f

