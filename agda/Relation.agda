open import Level


R : ∀ {l} (a : Set l) → (b : Set l) → Set (suc l)
R {l} a b = a → b → Set l
