import Relation.Binary.PropositionalEquality as Eq

open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

_∘_ : ∀ {a b c : Set} → (b → c) → (a → b) → a → c
_∘_ g f x = g (f x)

_∘'_ : ∀ {a b c : Set} → (b → c) → (a → b) → a → c
_∘'_ g f = λ x → g (f x)

postulate
  extensionality : ∀ {a b : Set} {f g : a → b}
    → (∀ (x : a) → f x ≡ g x)
      -----------------------
    →         f ≡ g

_+'_ : ℕ → ℕ → ℕ
m +' zero  = m
m +' suc n = suc (m +' n)

same-app : ∀ (m n : ℕ) → m +' n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
  helper : ∀ (m n : ℕ) → m +' n ≡ n + m
  helper m zero = refl
  helper m (suc n) = cong suc (helper m n)

same-partial : ∀ (m : ℕ) → (m +'_) ≡ (m +_)
same-partial m = extensionality (λ (n : ℕ) → same-app m n)

same : _+'_ ≡ _+_
same = extensionality (λ (m : ℕ) → same-partial m)

postulate
  ∀-extensionality : ∀ {a : Set} {b : a → Set} {f g : ∀ (x : a) → b x }
    → (∀ (x : a) → f x ≡ g x)
      -----------------------
    →          f ≡ g


-- \~- or \simeq for ≃
infix 0 _≃_

record _≃_ (a b : Set) : Set where
  field
    to      : a → b
    from    : b → a
    from∘to : ∀ (x : a) → from (to x) ≡ x
    to∘from : ∀ (y : b) → to (from y) ≡ y

open _≃_

-- record declaration is equivalent to an inductive data type declaration :

data _≃'_ (a b : Set) : Set where
  mk-≃' : ∀ (to   : a → b) →
          ∀ (from : b → a) →
          ∀ (from∘to : (∀ (x : a) → from (to x) ≡ x)) →
          ∀ (to∘from : (∀ (y : b) → to (from y) ≡ y)) →
          a ≃' b

to' : ∀ {a b : Set} → (a ≃' b) → (a → b)
to' (mk-≃' f _ _ _) = f

from' : ∀ {a b : Set} → (a ≃' b) → (b → a)
from' (mk-≃' _ g _ _) = g

from∘to' : ∀ {a b : Set} → (p : a ≃' b) → (∀ (x : a) → from' p (to' p x) ≡ x)
from∘to' (mk-≃' _ _ p _) = p

to∘from' : ∀ {a b : Set} → (p : a ≃' b) → (∀ (y : b) → to' p (from' p y) ≡ y)
to∘from' (mk-≃' _ _ _ q) = q

-- creating a value of type record
ℕ≃ℕ : ℕ ≃ ℕ
ℕ≃ℕ = record
  { to = λ x → x
  ; from = λ x → x
  ; from∘to = λ x → refl
  ; to∘from = λ x → refl
  }

≃-refl : ∀ {a : Set}
    ----------
  →   a ≃ a

≃-refl {a} = record
  { to = λ x → x
  ; from = λ x → x
  ; from∘to = λ x → refl
  ; to∘from = λ x → refl
  }

≃-sym : ∀ {a b : Set}
  →   a ≃ b
    ----------
  →   b ≃ a

≃-sym a≃b = record
  { to = from a≃b
  ; from = to a≃b
  ; from∘to = to∘from a≃b
  ; to∘from = from∘to a≃b
  }

≃-trans : ∀ {a b c : Set}
  →   a ≃ b
  →   b ≃ c
    ----------
  →   a ≃ c

≃-trans a≃b b≃c = record
  { to   = to b≃c ∘ to a≃b
  ; from = from a≃b ∘ from b≃c
  ; from∘to = λ x →
    begin
       from a≃b (from b≃c (to b≃c (to a≃b x)))
       ≡⟨ cong (from a≃b) (from∘to b≃c (to a≃b x)) ⟩
       from a≃b (to a≃b x)
       ≡⟨ from∘to a≃b x ⟩
       x
       ∎
  ; to∘from = λ x →
    begin
      to b≃c (to a≃b (from a≃b (from b≃c x)))
      ≡⟨ cong (to b≃c) (to∘from a≃b (from b≃c x)) ⟩
      to b≃c (from b≃c x)
      ≡⟨ to∘from b≃c x ⟩
      x
      ∎
  }

module ≃-Reasoning where

  infix 1 ≃-begin_
  infix 2 _≃⟨⟩_ _≃⟨_⟩_
  infix 3 _≃-∎

  ≃-begin_ : ∀ {a b : Set}
    →   a ≃ b
      ----------
    →   a ≃ b

  ≃-begin a≃b = a≃b

  _≃⟨⟩_ : ∀ (a : Set) {b : Set}
    →   a ≃ b
      ----------
    →   a ≃ b

  a ≃⟨⟩ a≃b = a≃b

  _≃⟨_⟩_ : ∀ (a : Set) {b c : Set}
    →   a ≃ b
    →   b ≃ c
      ---------
    →   a ≃ c

  a ≃⟨ a≃b ⟩ b≃c = ≃-trans a≃b b≃c


  _≃-∎ : ∀ (a : Set)
    ----------
    →   a ≃ a

  a ≃-∎ = ≃-refl

open ≃-Reasoning
