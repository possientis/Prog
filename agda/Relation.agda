open import Level
open import Data.Product using (∃; ∃-syntax; _×_) -- \x for ×, \ex for ∃

R : ∀ {l} (a : Set l) → (b : Set l) → Set (suc l)
R {l} a b = a → b → Set l

_∘_ : ∀ {l} {a b c : Set l} → R b c → R a b → R a c
_∘_ s r x z = ∃[ y ] ( r x y × s y z)


