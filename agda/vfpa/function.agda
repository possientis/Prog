module function where

_∘_ : ∀ {ℓ ℓ' ℓ''}{a : Set ℓ}{b : Set ℓ'}{c : Set ℓ''} → (b → c) → (a → b) → (a → c)
(g ∘ f) x = g (f x) 


