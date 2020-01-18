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


module ≡-Reasoning {a : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : a}
    →   x ≡ y
      ----------
    →   x ≡ y

  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ (x : a) {y : a}
    →   x ≡ y
      ----------
    →   x ≡ y

  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : a) {y z : a}
    →   x ≡ y
    →   y ≡ z
      ----------
    →   x ≡ z

  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : a)
      ----------
    →  x ≡ x

  x ∎ = refl


open ≡-Reasoning


trans' : ∀ {a : Set} {x y z : a}
  →   x ≡ y
  →   y ≡ z
    ----------
  →   x ≡ z

trans' {a} {x} {y} {z} x≡y y≡z =
  begin
    x
    ≡⟨ x≡y ⟩
    y
    ≡⟨ y≡z ⟩
    z
    ∎

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
    ≡⟨ +-identity m ⟩
    m
    ≡⟨⟩
    zero + m
    ∎
+-comm m (suc n) =
  begin
    m + suc n
    ≡⟨ +-suc m n ⟩
    suc (m + n)
    ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
    ≡⟨⟩
    suc n + m
    ∎




