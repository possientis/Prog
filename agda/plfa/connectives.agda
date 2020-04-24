module connectives where

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
  inj₁ : a → a ⊎ b
  inj₂ : b → a ⊎ b


case-⊎ : ∀ {a b c : Set}
  →   (a → c)
  →   (b → c)
  →    a ⊎ b
    ----------
  →      c

case-⊎ a→c b→c (inj₁ x) = a→c x
case-⊎ a→c b→c (inj₂ y) = b→c y

η-⊎ : ∀ {a b : Set} (w : a ⊎ b) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ x) = refl

uniq-⊎ : ∀ {a b c : Set} (h : a ⊎ b → c) (w : a ⊎ b) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ x) = refl

infixr 1 _⊎_

⊎-to : ∀ {a b : Set} → a ⊎ b → b ⊎ a
⊎-to (inj₁ x) = inj₂ x
⊎-to (inj₂ x) = inj₁ x

⊎-idem : ∀ {a b : Set} → (x : a ⊎ b) → ⊎-to (⊎-to x) ≡ x
⊎-idem (inj₁ x) = refl
⊎-idem (inj₂ x) = refl

⊎-comm : ∀ (a b : Set) → a ⊎ b ≃ b ⊎ a
⊎-comm a b = record
  { to = ⊎-to
  ; from = ⊎-to
  ; from∘to = ⊎-idem
  ; to∘from = ⊎-idem
  }

⊎-assoc-to : ∀ {a b c : Set} → (a ⊎ b) ⊎ c → a ⊎ (b ⊎ c)
⊎-assoc-to (inj₁ (inj₁ x)) = inj₁ x
⊎-assoc-to (inj₁ (inj₂ x)) = inj₂ (inj₁ x)
⊎-assoc-to (inj₂ x) = inj₂ (inj₂ x)


⊎-assoc-from : ∀ {a b c : Set} → a ⊎ (b ⊎ c) → (a ⊎ b) ⊎ c
⊎-assoc-from (inj₁ x) = inj₁ (inj₁ x)
⊎-assoc-from (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
⊎-assoc-from (inj₂ (inj₂ x)) = inj₂ x

⊎-assoc-from∘to : ∀ {a b c : Set} (x : (a ⊎ b) ⊎ c) → ⊎-assoc-from (⊎-assoc-to x) ≡ x
⊎-assoc-from∘to (inj₁ (inj₁ x)) = refl
⊎-assoc-from∘to (inj₁ (inj₂ x)) = refl
⊎-assoc-from∘to (inj₂ x) = refl

⊎-assoc-to∘from : ∀ {a b c : Set} (x : a ⊎ (b ⊎ c)) → ⊎-assoc-to (⊎-assoc-from x) ≡ x
⊎-assoc-to∘from (inj₁ x) = refl
⊎-assoc-to∘from (inj₂ (inj₁ x)) = refl
⊎-assoc-to∘from (inj₂ (inj₂ x)) = refl

⊎-assoc : ∀ {a b c : Set} → (a ⊎ b) ⊎ c ≃ a ⊎ (b ⊎ c)
⊎-assoc = record
  { to = (λ { (inj₁ (inj₁ x)) → inj₁ x
            ; (inj₁ (inj₂ y)) → inj₂ (inj₁ y)
            ; (inj₂ z) → inj₂ (inj₂ z)
            })
  ; from = ⊎-assoc-from
  ; from∘to = (λ { (inj₁ (inj₁ x)) → refl ; (inj₁ (inj₂ y)) → refl ; (inj₂ z) → refl })
  ; to∘from = λ{(inj₁ x) → refl ; (inj₂ (inj₁ y)) → refl ; (inj₂ (inj₂ z)) → refl}
  }

-- \bot for ⊥
data ⊥ : Set where
  -- no clauses !

⊥-elim : ∀ {a : Set}
  →    ⊥
    --------
  →    a

⊥-elim ()

uniq-⊥ : ∀ {a : Set} (h : ⊥ → a) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()


⊥-identity-l : ∀ {a : Set} → ⊥ ⊎ a ≃ a
⊥-identity-l = record
  { to = λ { (inj₂ x) → x}
  ; from = inj₂
  ; from∘to = λ {(inj₂ x) → refl}
  ; to∘from = λ { y → refl}
  }

⊥-identity-r : ∀ {a : Set} → a ⊎ ⊥ ≃ a
⊥-identity-r = record
  { to = λ { (inj₁ x) → x}
  ; from = inj₁
  ; from∘to = λ { (inj₁ x) → refl}
  ; to∘from = λ {y → refl}
  }


→-elim : ∀ {a b : Set}
  →    (a → b)
  →    a
     ----------
  →    b

→-elim f x = f x


η-→ : ∀ {a b : Set} (f : a → b) → (λ (x : a) → f x) ≡ f
η-→ f = refl

currying : ∀ {a b c : Set} → (a → b → c) ≃ (a × b → c)
currying = record
  { to = λ {f → λ { ⟨ x , y ⟩ → f x y}}
  ; from = λ {g → λ {x → λ {y → g ⟨ x , y ⟩}}}
  ; from∘to = λ { f → refl}
  ; to∘from = λ { g → extensionality λ { ⟨ x , y ⟩ → refl} }
  }

-- the name does not really reflect situation here
→-distrib-⊎-r : ∀ {a b c : Set} → (a ⊎ b → c) ≃ (a → c) × (b → c)
→-distrib-⊎-r = record
  { to = λ{f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩}
  ; from = λ{⟨ f , g ⟩ → λ{(inj₁ x) → f x ; (inj₂ y) → g y}}
  ; from∘to = λ{ f → extensionality (λ{(inj₁ x) → refl ; (inj₂ y) → refl})}
  ; to∘from = λ{⟨ f , g ⟩ → refl}
  }

→-distrib-×-l : ∀ {a b c : Set} → (a → b × c) ≃ (a → b) × (a → c)
→-distrib-×-l = record
  { to = λ{f → ⟨ proj₁ ∘ f ,  proj₂ ∘ f ⟩}
  ; from = λ{⟨ f , g ⟩ → λ{x → ⟨ f x , g x ⟩}}
  ; from∘to = λ {f → extensionality (λ{x → η-× (f x)})}
  ; to∘from = λ{⟨ f , g ⟩ → refl}
  }

×-distrib-⊎-r : ∀ {a b c : Set} → (a ⊎ b) × c ≃ (a × c) ⊎ (b × c)
×-distrib-⊎-r = record
  { to      = λ {⟨ (inj₁ x) , z ⟩ → inj₁ ⟨ x , z ⟩
                ;⟨ (inj₂ y) , z ⟩ → inj₂ ⟨ y , z ⟩
                }
  ; from    = λ {(inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
                ;(inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩
                }
  ; from∘to = λ {⟨ (inj₁ x) , z ⟩ → refl
                ;⟨ (inj₂ y) , z ⟩ → refl
                }
  ; to∘from = λ {(inj₁ ⟨ x , y ⟩) → refl
                ;(inj₂ ⟨ y , z ⟩) → refl
                }
  }

-- only an embedding here
⊎-distrib-×-r : ∀ {a b c : Set} → (a × b) ⊎ c ≲ (a ⊎ c) × (b ⊎ c)
⊎-distrib-×-r = record
  { to      = λ {(inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
                ;(inj₂ z) → ⟨ inj₂ z , inj₂ z ⟩
                }
  ; from    = λ {⟨ (inj₁ x) , (inj₁ y) ⟩ → inj₁ ⟨ x , y ⟩
                ;⟨ (inj₂ z) , _ ⟩ → inj₂ z
                ;⟨ (inj₁ _) , (inj₂ z) ⟩ → inj₂ z
                }
  ; from∘to = λ {(inj₁ ⟨ x , y ⟩) → refl
                ; (inj₂ z) → refl
                }
  }

⊎-weak-× : ∀ {a b c : Set} → (a ⊎ b) × c → a ⊎ (b × c)
⊎-weak-× ⟨ inj₁ x , z ⟩ = inj₁ x
⊎-weak-× ⟨ inj₂ y , z ⟩ = inj₂ ⟨ y , z ⟩


⊎×-implies-×⊎ : ∀ {a b c d : Set} → (a × b) ⊎ (c × d) → (a ⊎ c) × (b ⊎ d)
⊎×-implies-×⊎ (inj₁ ⟨ x , y ⟩) = ⟨ inj₁ x , inj₁ y ⟩
⊎×-implies-×⊎ (inj₂ ⟨ z , t ⟩) = ⟨ inj₂ z , inj₂ t ⟩
