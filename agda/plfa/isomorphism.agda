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



