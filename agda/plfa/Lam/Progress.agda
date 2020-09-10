module Lam.Progress where

open import Lam.Value
open import Lam.Syntax
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
