module reflect-list where

open import bool
open import list
open import level

data 𝕄 : Set -> Set ℓ₁ where
  Inj  : {a : Set} → 𝕃 a → 𝕄 a
  App  : {a : Set} → 𝕄 a → 𝕄 a → 𝕄 a
  Map  : {a b : Set} → (a → b) → 𝕄 a → 𝕄 b
  Cons : {a : Set} → a → 𝕄 a → 𝕄 a
  Nil  : {a : Set} → 𝕄 a

𝕃⟦_⟧ : {a : Set} → 𝕄 a -> 𝕃 a
𝕃⟦ Inj xs ⟧   = xs
𝕃⟦ App r s ⟧  = 𝕃⟦ r ⟧ ++ 𝕃⟦ s ⟧
𝕃⟦ Map f r ⟧  = map f 𝕃⟦ r ⟧
𝕃⟦ Cons x r ⟧ = x ∷ 𝕃⟦ r ⟧
𝕃⟦ Nil ⟧      = []

is-empty : {a : Set} → 𝕄 a → 𝔹
is-empty (Inj [])      = tt
is-empty (Inj (_ ∷ _)) = ff
is-empty (App r1 r2)   = is-empty r1 && is-empty r2
is-empty (Map _ r)     = is-empty r
is-empty (Cons _ _)    = ff
is-empty Nil           = tt

simplify : {a : Set} → 𝕄 a → 𝕄 a
simplify (App (Inj xs) r2)     = if is-empty r2
  then Inj xs
  else App (Inj xs) r2
simplify (App (App r1 r1') r2) = App r1 (App r1' r2)
simplify (App (Map f r1) r2)   = if is-empty r2
  then Map f r1
  else App (Map f r1) r2
simplify (App (Cons x r1) r2)  = Cons x (App r1 r2)
simplify (App Nil r2)          = r2
simplify (Inj xs)              = Inj xs
simplify (Map x r) = {!!}
simplify (Cons x r) = {!!}
simplify Nil = {!!}

