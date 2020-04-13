open import Data.Nat using (ℕ; suc)

data ImageOf {a b : Set} (f : a → b) : b → Set where
  Imf : ∀ (x : a) → ImageOf f (f x)

inverse : ∀ {a b : Set} → {f : a → b} → {y : b} → ImageOf f y → a
inverse (Imf x) = x

data Vec {a : Set} : ℕ → Set where
  Nil  : Vec {a} 0
  Cons : ∀ {n : ℕ} → a → Vec {a} n → Vec {a} (suc n)
