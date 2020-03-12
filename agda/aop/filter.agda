open import Data.List using (List; _∷_; []; concat; map)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false)
open import Function using (_∘_)

_~>_,_ : ∀ {a b : Set} → (a → Bool) → (a → b) → (a → b) → a → b
(p ~> f , g) x with p x
(p ~> f , g) x | false = g x
(p ~> f , g) x | true = f x

nilp : ∀ {a : Set} → a → List a
nilp x = []

wrap : ∀ {a : Set} → a → List a
wrap x = x ∷ []

filter : ∀ {a : Set} → (a → Bool) → List a → List a
filter {a} p = concat ∘ map (p ~> wrap , nilp)





