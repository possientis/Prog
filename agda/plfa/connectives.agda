import Relation.Binary.PropositionalEquality as Eq 
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import isomorphism using (_≃_; _≲_; _⇔_; extensionality)
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

×-comm : ∀ {a b : Set} → a × b ≃ b × a
×-comm = record
  { to = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
  ; from = λ { ⟨ y , x ⟩ → ⟨ x , y ⟩}
  ; from∘to = λ { ⟨ x , y ⟩ → refl}
  ; to∘from = λ { ⟨ x , y ⟩ → refl}
  }


×-assoc : ∀ {a b c : Set} → (a × b) × c ≃ a × (b × c)
×-assoc = record
  { to = λ { ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩}
  ; from = λ { ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩}
  ; from∘to = λ { ⟨ ⟨ x , y ⟩ , z ⟩ →  refl}
  ; to∘from = λ { ⟨ x , ⟨ y , z ⟩ ⟩ →  refl}
  }

open _⇔_

⇔-to-× : ∀ {a b : Set} → a ⇔ b → (a → b) × (b → a)
⇔-to-× r = ⟨ to r , from r ⟩

×-to-⇔ : ∀ {a b : Set} → (a → b) × (b → a) → a ⇔ b
×-to-⇔ ⟨ x , y ⟩ = record { to = x; from = y}

from-⇔-to-× : ∀ {a b : Set} (x : a ⇔ b) → ×-to-⇔ (⇔-to-× x) ≡ x
from-⇔-to-× record { to = to ; from = from } = refl

⇔≃× : ∀ {a b : Set} → a ⇔ b ≃ (a → b) × (b → a)
⇔≃× = record
  { to = ⇔-to-×
  ; from = ×-to-⇔
  ; from∘to = from-⇔-to-×
  ; to∘from = {!!}
  }
