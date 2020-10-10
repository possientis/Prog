module Lam.Eval where

open import Data.Nat         using (ℕ; zero; suc)

open import Lam.Type
open import Lam.Value
open import Lam.Typing
open import Lam.Syntax
open import Lam.Closure
open import Lam.Context
open import Lam.Progress
open import Lam.Preservation


record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished (N : Term) : Set where

  done :
      Value N
    ----------
    → Finished N

  out-of-gas :
    ----------
      Finished N

data Steps (L : Term) : Set where

  steps : ∀ {N : Term}
    → L —↠ N
    → Finished N
      ----------
    → Steps L

eval : ∀ {L : Term} {A : Type}
  → Gas
  → ∅ ⊢ L ∶ A
    ----------
  → Steps L

eval {L} (gas zero) p = steps (L ∎) out-of-gas
eval {L} (gas (suc m)) p with progress p
... | done q = steps (L ∎) (done q)
eval {L} (gas (suc m)) p | step {N} q with eval (gas m) (preserve p q)
... | steps r s = steps (L —→⟨ q ⟩ r) s
