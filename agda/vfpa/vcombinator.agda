module vcombinator where

open import nat

data VComb : Set where
    S   : VComb
    K   : VComb
    App : VComb → VComb → VComb
    Var : ℕ → VComb

{-
λ* : ℕ → VComb → VComb
λ* n S = App K S
λ* n K = App K K
λ* n (App c₁ c₂) = App (App S (λ* n c₁)) (λ* n c₂)
λ* n (Var x) = {!!}
-}
