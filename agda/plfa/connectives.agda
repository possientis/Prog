import Relation.Binary.PropositionalEquality as Eq 
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import isomorphism using (_≃_; _≲_; extensionality)
open isomorphism.≃-Reasoning

-- \x for ×
data _×_ (a b : Set) : Set where
  ⟨_,_⟩ :
       a
    →  b
      ----
    → a × b

proj₁ : ∀ {a b : Set}

  →   a × b
    ---------
  →   a

proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {a b : Set}

  →   a × b
    ---------
  →   b

proj₂ ⟨ x , y ⟩ = y


η-× : ∀ {a b : Set} (w : a × b) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_


