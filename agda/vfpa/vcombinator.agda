module vcombinator where

open import nat

data VComb : Set where
    S   : VComb
    K   : VComb
    App : VComb → VComb → VComb
    Var : ℕ → VComb
