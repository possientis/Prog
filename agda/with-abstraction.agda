module with-abstraction where

open import nat
open import bool
open import id


data 𝕃 {ℓ} (a : Set ℓ) : Set ℓ where
  []  : 𝕃 a
  _∷_ : a → 𝕃 a → 𝕃 a

infixr 5 _∷_

filter : ∀ {ℓ} {a : Set ℓ} → (a → 𝔹) → 𝕃 a → 𝕃 a
filter p []            = []
filter p (x ∷ xs) with p x
filter p (x ∷ xs) | tt = x ∷ filter p xs
filter p (x ∷ xs) | ff =     filter p xs


filter' : ∀ {ℓ} {a : Set ℓ} → (a → 𝔹) → 𝕃 a → 𝕃 a
filter' p [] = []
filter' p (x ∷ xs) with p x
... | tt     = x ∷ filter p xs
... | ff     =     filter p xs
