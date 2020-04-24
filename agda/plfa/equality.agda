module equality where

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc) -- \sqcup for ⊔

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

{-# BUILTIN EQUALITY _≡_ #-}


data even : ℕ → Set
data odd  : ℕ → Set

-- Overloading of defined names is not allowed. But constructors are fine.

data even where
  zero :           -- overloaded constructor
     ----------
     even zero

  suc : ∀ {n : ℕ}  -- overloaded constructor
    → odd n
      ----------
    → even (suc n)

data odd where

  suc : ∀ {n : ℕ}  -- more overloading
    → even n
      ----------
    → odd (suc n)


even-comm : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)

even-comm m n ev rewrite +-comm  m n = ev


+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' zero n rewrite +-identity n = refl
+-comm' (suc m) n rewrite +-suc n m | +-comm' m n = refl


even-comm' : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)

even-comm' m n ev with (m + n) | +-comm m n
even-comm' m n ev | .(n + m) | refl = ev

even-comm'' : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)

even-comm'' m n = subst even (+-comm m n)

-- \.= for ≐
_≐_ : ∀ {a : Set} (x y : a) → Set₁         -- need Set₁ here, not Set
_≐_ {a} x y = ∀ (P : a → Set) → P x → P y  -- need 'a' in scope, so not writing x ≐ y


refl-≐ : ∀ {a : Set} {x : a}
    --------------------------
  →         x ≐ x

refl-≐ P Px = Px


trans-≐ : ∀ {a : Set} {x y z : a}
  →   x ≐ y
  →   y ≐ z
     ----------
  →   x ≐ z

trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)


sym-≐ : ∀ {a : Set} {x y : a}
  →   x ≐ y
     ----------
  →   y ≐ x

sym-≐ {a} {x} {y} x≐y P Py = x≐y Q Qx Py
  where
  Q : a → Set
  Q z = P z → P x
  Qx : Q x
  Qx Px = Px

≡-implies-≐ : ∀ {a : Set} {x y : a}
  →   x ≡ y
    ----------
  →   x ≐ y

≡-implies-≐ x≡y P Px = subst P x≡y Px


≐-implies-≡ : ∀ {a : Set} {x y : a}
  →   x ≐ y
    ----------
  →   x ≡ y

≐-implies-≡ {a} {x} {y} x≐y = x≐y Q refl
  where
  Q : a → Set
  Q z = x ≡ z

-- \ell for ℓ
data _≡'_ {ℓ : Level} {a : Set ℓ} (x : a) : a → Set ℓ where
  refl' : x ≡' x

sym' : {ℓ : Level} {a : Set ℓ} {x y : a}
  →    x ≡' y
     ----------
  →    y ≡' x

sym' refl' = refl'

-- \.= for ≐
_≐'_ : ∀ {ℓ : Level} {a : Set ℓ} (x y : a) → Set (lsuc ℓ)
_≐'_ {ℓ} {a} x y = ∀ (P : a → Set ℓ) → P x → P y


-- \circ for ∘
_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {a : Set ℓ₁} {b : Set ℓ₂} {c : Set ℓ₃}
    → (b → c) → (a → b) → a → c

_∘_ g f x = g (f x)

