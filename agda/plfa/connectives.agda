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

to-× : ∀ {a b : Set} → a ⇔ b → (a → b) × (b → a)
to-× r = ⟨ to r , from r ⟩

from-× : ∀ {a b : Set} → (a → b) × (b → a) → a ⇔ b
from-× ⟨ x , y ⟩ = record { to = x; from = y}

from∘to-× : ∀ {a b : Set} (x : a ⇔ b) → from-× (to-× x) ≡ x
from∘to-× record { to = to ; from = from } = refl

to∘from-× : ∀ {a b : Set} (p : (a → b) × (b → a)) → (to-× (from-× p) ≡ p)
to∘from-× ⟨ x , y ⟩ = refl

⇔≃× : ∀ {a b : Set} → a ⇔ b ≃ (a → b) × (b → a)
⇔≃× = record
  { to = to-×
  ; from = from-×
  ; from∘to = from∘to-×
  ; to∘from = to∘from-×
  }


data ⊤ : Set where  -- \top for ⊤
  tt : ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl


⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identity-l : ∀ {a : Set} → ⊤ × a ≃ a
⊤-identity-l = record
  { to = λ { ⟨ tt , x ⟩ → x}
  ; from = λ x → ⟨ tt , x ⟩
  ; from∘to = λ { ⟨ tt , x ⟩ → refl}
  ; to∘from = λ { x → refl}
  }

⊤-identity-r : ∀ {a : Set} → a × ⊤ ≃ a
⊤-identity-r = record
  { to = λ { ⟨ x , tt ⟩ → x}
  ; from = λ { x → ⟨ x , tt ⟩}
  ; from∘to = λ {⟨ x , tt ⟩ → refl}
  ; to∘from = λ {x → refl}
  }

data _⊎_ (a b : Set) : Set where
  inj1 : a → a ⊎ b
  inj2 : b → a ⊎ b


case-⊎ : ∀ {a b c : Set}
  →   (a → c)
  →   (b → c)
  →    a ⊎ b
    ----------
  →      c

case-⊎ a→c b→c (inj1 x) = a→c x
case-⊎ a→c b→c (inj2 y) = b→c y

η-⊎ : ∀ {a b : Set} (w : a ⊎ b) → case-⊎ inj1 inj2 w ≡ w
η-⊎ (inj1 x) = refl
η-⊎ (inj2 x) = refl

uniq-⊎ : ∀ {a b c : Set} (h : a ⊎ b → c) (w : a ⊎ b) →
  case-⊎ (h ∘ inj1) (h ∘ inj2) w ≡ h w
uniq-⊎ h (inj1 x) = refl
uniq-⊎ h (inj2 x) = refl

infixr 1 _⊎_

⊎-comm : ∀ (a b : Set) → a ⊎ b ≃ b ⊎ a
⊎-comm a b = record
  { to = {!!} 
  ; from = {!!}
  ; from∘to = {!!}
  ; to∘from = {!!}
  }
