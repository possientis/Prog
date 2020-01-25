import Relation.Binary.PropositionalEquality as Eq

open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

_∘_ : ∀ {a b c : Set} → (b → c) → (a → b) → a → c
_∘_ g f x = g (f x)

_∘'_ : ∀ {a b c : Set} → (b → c) → (a → b) → a → c
_∘'_ g f = λ x → g (f x)



