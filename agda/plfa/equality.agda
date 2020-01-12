data _≡_ {a : Set} (x : a) : a -> Set where -- \==
  refl : x ≡ x

infix 4 _≡_


sym : ∀ {a : Set} {x y : a}
  →   x ≡ y
    ----------
  →   y ≡ x

sym refl = refl

trans : ∀ {a : Set} {x y z : a}
  →   x ≡ y
  →   y ≡ z
    ----------
  →   x ≡ z

trans refl q = q

cong : ∀ {a b : Set} (f : a → b) {x y : a}
  →   x ≡ y
    ----------
  →   f x ≡ f y

cong f refl = refl

cong₂ : ∀ {a b c : Set} (f : a → b → c) {u x : a} {v y : b}
  →   u ≡ x
  →   v ≡ y
    ----------
  →   f u v ≡ f x y

cong₂ f refl refl = refl


cong-app : ∀ {a b : Set} {f g : a → b}
  →   f ≡ g
    ----------
  → ∀ (x : a) → f x ≡ g x

cong-app refl x = refl

subst : ∀ {a : Set} {x y : a} (P : a → Set)
  →   x ≡ y
    ----------
  →   P x → P y

subst P refl px = px
