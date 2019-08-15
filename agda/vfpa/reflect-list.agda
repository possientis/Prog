module reflect-list where

open import level
open import list

data 𝕄 : Set -> Set ℓ₁ where
  Inj  : {a : Set} → 𝕃 a → 𝕄 a
  App  : {a : Set} → 𝕄 a → 𝕄 a → 𝕄 a
  Map  : {a b : Set} → (a → b) → 𝕄 a → 𝕄 b
  Cons : {a : Set} → a → 𝕄 a → 𝕄 a
  Nil  : {a : Set} → 𝕄 a
