module with-abstraction where

open import bool
open import list

filter' : ∀ {ℓ} {a : Set ℓ} → (a → 𝔹) → 𝕃 a → 𝕃 a
filter' p [] = []
filter' p (x ∷ xs) with p x
... | tt     = x ∷ filter p xs
... | ff     =     filter p xs
