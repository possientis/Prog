module list where

open import nat
open import bool

data 𝕃 {ℓ} (a : Set ℓ) : Set ℓ where
  []  : 𝕃 a
  _∷_ : a → 𝕃 a → 𝕃 a

infixr 5 _∷_

length :  ∀ {ℓ} {a : Set ℓ} → 𝕃 a → ℕ
length []       = 0
length (x ∷ xs) = succ (length xs)

_++_ : ∀ {ℓ} {a : Set ℓ} → 𝕃 a → 𝕃 a → 𝕃 a
[] ++ ys       = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

infixr 6 _++_

map : ∀ {ℓ ℓ'} {a : Set ℓ} {b : Set ℓ'} → (a → b) → 𝕃 a → 𝕃 b
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

filter : ∀ {ℓ} {a : Set ℓ} → (a → 𝔹) → 𝕃 a → 𝕃 a
filter p []       = []
filter p (x ∷ xs) = let ys = filter p xs in if p x then x ∷ ys else ys


remove : ∀ {ℓ} {a : Set ℓ} (eq : a → a → 𝔹) (x : a) → 𝕃 a → 𝕃 a
remove eq a xs = filter (λ x → ¬ eq a x) xs
