import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_;_*_)
open import Data.Nat.Properties using (+-comm;*-comm)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ}
      -----------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n


_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

infix 4 _≤_             -- binds less tightly than _+_

_ : 1 + 2 ≤ 3           -- no paranthesis needed
_ = s≤s (s≤s (s≤s z≤n)) -- way more verbose than coq's le_n

inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n

inv-s≤s (s≤s m≤n) = m≤n


inv-z≤n : ∀ {n : ℕ}
  → n ≤ zero
    --------
  → n ≡ zero

inv-z≤n z≤n = refl


≤-refl : ∀ {n : ℕ}
    ---------
  → n ≤ n

≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
  ----------
  → m ≤ p

≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)


≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
  ----------
  → m ≡ n

≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)


data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n


data Total' : ℕ → ℕ → Set where

  forward' : ∀ {m n : ℕ}
    →  m ≤ n
      ---------
    → Total' m n

  flipped' : ∀ {m n : ℕ}
    →  n ≤ m
      ---------
    → Total' m n


≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
≤-total (suc m) (suc n) | forward m≤n = forward (s≤s m≤n)
≤-total (suc m) (suc n) | flipped n≤m = flipped (s≤s n≤m)


≤-total' : ∀ (m n : ℕ) → Total m n
≤-total' zero n = forward z≤n
≤-total' (suc m) zero = flipped z≤n
≤-total' (suc m) (suc n) = helper (≤-total' m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n) = forward (s≤s m≤n)
  helper (flipped n≤m) = flipped (s≤s n≤m)


+-mono-r-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    ---------
  → n + p ≤ n + q

+-mono-r-≤ zero p q p≤q = p≤q
+-mono-r-≤ (suc n) p q p≤q = s≤s (+-mono-r-≤ n p q p≤q)

+-mono-l-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    ---------
  → m + p ≤ n + p

+-mono-l-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-mono-r-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    ---------
  → m + p ≤ n + q

+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-mono-l-≤ m n p m≤n) (+-mono-r-≤ n p q p≤q)


*-mono-r-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    ---------
  → n * p ≤ n * q

*-mono-r-≤ zero p q p≤q = z≤n
*-mono-r-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-mono-r-≤ n p q p≤q)

*-mono-l-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    ---------
  → m * p ≤ n * p

*-mono-l-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-mono-r-≤ p m n m≤n


*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    ---------
  → m * p ≤ n * q

*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-mono-l-≤ m n p m≤n) (*-mono-r-≤ n p q p≤q)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      -----------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n



≤-< : ∀ {m n : ℕ}
  → suc m ≤ n
    -------------
  → m < n

≤-< {zero} (s≤s m≤n) = z<s
≤-< {suc m} (s≤s m≤n) = s<s (≤-< m≤n)

<-≤ : ∀ {m n : ℕ}
  → m < n
    -------------
  → suc m ≤ n

<-≤ z<s = s≤s z≤n
<-≤ (s<s m<n) = s≤s (<-≤ m<n)


<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
    ----------
  → m < p

<-trans z<s (s<s _) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

<-imp-≤ : ∀ {m n : ℕ}
  → m < n
    --------
  → m ≤ n

<-imp-≤ z<s = z≤n
<-imp-≤ (s<s m<n) = s≤s (<-imp-≤ m<n)


data Trichotomy (m n : ℕ) : Set where
  Less  : m < n → Trichotomy m n
  Equal : m ≡ n → Trichotomy m n
  More  : n < m → Trichotomy m n


trichotomy : ∀ (m n : ℕ) → Trichotomy m n 
trichotomy zero zero = Equal refl
trichotomy zero (suc n) = Less z<s
trichotomy (suc m) zero = More z<s
trichotomy (suc m) (suc n) with trichotomy m n
trichotomy (suc m) (suc n) | Less m<n = Less (s<s m<n)
trichotomy (suc m) (suc n) | Equal m≡n = Equal (cong suc m≡n)
trichotomy (suc m) (suc n) | More m>n = More (s<s m>n)

+-mono-r-< : ∀ (n p q : ℕ)
  → p < q
    ----------
  → n + p < n + q

+-mono-r-< zero p q p<q = p<q
+-mono-r-< (suc n) p q p<q = s<s (+-mono-r-< n p q p<q)

+-mono-l-< : ∀ (m n p : ℕ)
  → m < n
    ----------
  → m + p < n + p

+-mono-l-< m n p m<n rewrite +-comm m p | +-comm n p = +-mono-r-< p m n m<n


+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
    ----------
  → m + p < n + q

+-mono-< m n p q m<n p<q = <-trans (+-mono-l-< m n p m<n) (+-mono-r-< n p q p<q)

<-trans' : ∀ {m n p : ℕ}
  → m < n
  → n < p
    ----------
  → m < p

<-trans' m<n n<p = ≤-< (≤-trans (<-≤ m<n) (<-imp-≤ n<p))

-- mutually recursive datatypes

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


e+e≡e : ∀ {m n : ℕ}
  →  even m
  →  even n
    ----------
  →  even (m + n)


o+e≡o : ∀ {m n : ℕ}
  →  odd m
  →  even n
    ----------
  →  odd (m + n)

e+e≡e zero en = en
e+e≡e (suc om) en = suc (o+e≡o om en)

o+e≡o (suc em) en = suc (e+e≡e em en)


e+o≡o : ∀ {m n : ℕ}
  →  even m
  →  odd n
    ----------
  →  odd (m + n)

e+o≡o {m} {n} em on rewrite +-comm m n = o+e≡o on em

o+o≡e : ∀ {m n : ℕ}
  →  odd m
  →  odd n
    ----------
  →  even (m + n)

o+o≡e (suc em) on = suc (e+o≡o em on)



