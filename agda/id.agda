module id where

data _≡_ {ℓ} {X : Set ℓ} : X → X → Set ℓ where
  refl : (x : X) -> x ≡ x

infixr 4 _≡_

≡-refl : ∀{ℓ} {X : Set ℓ} (x : X) → x ≡ x
≡-refl x = refl _

≡-sym : ∀{ℓ} {X : Set ℓ} {x y : X} → x ≡ y → y ≡ x
≡-sym (refl x) = refl _

≡-trans : ∀ {ℓ} {X : Set ℓ} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
≡-trans (refl x) (refl y) = refl x

ap : ∀ {ℓ} {ℓ'} {X : Set ℓ} {Y : Set ℓ'} {x y : X} (f : X → Y) → x ≡ y → f x ≡ f y
ap f (refl x) = refl (f x) 

data Singleton {ℓ} {X : Set ℓ} (x : X) : Set ℓ where
  _with≡_ : (y : X) → x ≡ y → Singleton x


inspect : ∀ {ℓ} {X : Set ℓ} (x : X) → Singleton x
inspect x = x with≡ (refl x)

{-# BUILTIN EQUALITY _≡_ #-}

data _+_ {ℓ} : Set ℓ → Set ℓ -> Set ℓ where
  left  : {a b : Set ℓ} → (x : a) → a + b
  right : {a b : Set ℓ} → (x : b) → a + b

