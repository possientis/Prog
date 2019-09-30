module nat where

open import id
open import sum
open import bool
open import void
open import relations
import min-max as minmax

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero   + y = y
succ x + y = succ (x + y)

succ-not-0 : (n : ℕ) → ¬ (succ n ≡ 0)
succ-not-0 n ()

+-n+O : (n : ℕ)→ n + 0 ≡ n
+-n+O zero     = refl 0
+-n+O (succ n) = ap succ (+-n+O n)

+-assoc : (n m p : ℕ) → (n + m) + p ≡ n + (m + p)
+-assoc zero m p     = refl (m + p)
+-assoc (succ n) m p = ap succ (+-assoc n m p)

+-n+succ : (n m : ℕ) → n + succ m ≡ succ (n + m)
+-n+succ zero m     = refl (succ m)
+-n+succ (succ n) m = ap succ (+-n+succ n m)

+-comm : (n m : ℕ) → n + m ≡ m + n
+-comm zero m     = ≡-sym (+-n+O m)
+-comm (succ n) m = ≡-trans (ap succ (+-comm n m)) (≡-sym (+-n+succ m n))

infix 5 _+_
infix 6 _*_

_*_ : ℕ → ℕ → ℕ
zero * m = 0
succ n * m = m + n * m

*-distribr : (n m p : ℕ) → (n + m) * p ≡ n * p + m * p
*-distribr zero m p     = refl (m * p)
*-distribr (succ n) m p = ≡-trans
  (ap (λ x → p + x) (*-distribr n m p))
  (≡-sym (+-assoc p (n * p) (m * p)))

*-n*0 : (n : ℕ) → n * 0 ≡ 0
*-n*0 zero     = refl 0
*-n*0 (succ n) = *-n*0 n

*-n*succ : (n m : ℕ) → n * succ m ≡ n + n * m
*-n*succ zero m     = refl 0
*-n*succ (succ n) m = ap succ
  (≡-trans
    (≡-trans
      (≡-trans
        (ap (λ x → m + x) (*-n*succ n m))
        (≡-sym (+-assoc m n (n * m))))
      (ap (λ x → x + n * m) (+-comm m n)))
     (+-assoc n m (n * m)))


*-comm : (n m : ℕ) → n * m ≡ m * n
*-comm zero m     = ≡-sym (*-n*0 m)
*-comm (succ n) m = ≡-sym
  (≡-trans
    (*-n*succ m n)
    (ap (λ x → m + x) (≡-sym (*-comm n m)))) 


*-assoc : (n m p : ℕ) → (n * m) * p ≡ n * (m * p)
*-assoc zero m p     = refl 0
*-assoc (succ n) m p = ≡-trans
  (*-distribr m (n * m) p)
  (ap (λ x → m * p + x) (*-assoc n m p))

is-even : ℕ → 𝔹
is-odd  : ℕ → 𝔹
is-even zero = tt
is-even (succ n) = is-odd n
is-odd zero = ff
is-odd (succ n) = is-even n

pred : (n : ℕ) → ℕ
pred zero     = 0
pred (succ n) = n

data _≤_ : ℕ → ℕ → Set where
  le-n : (n : ℕ)   → n ≤ n
  le-s : {n m : ℕ} → n ≤ m → n ≤ succ m 

infixr 4 _≤_


≤-refl : (n : ℕ) → n ≤ n
≤-refl n = le-n n

≤-trans : {n m p : ℕ} → n ≤ m → m ≤ p → n ≤ p
≤-trans p (le-n n) = p
≤-trans p (le-s q) = le-s (≤-trans p q)

≤-n-s : {n m : ℕ} → n ≤ m → succ n ≤ succ m
≤-n-s (le-n n) = le-n (succ n)
≤-n-s (le-s p) = le-s (≤-n-s p)

≤-s-n : {n m : ℕ} → succ n ≤ succ m → n ≤ m
≤-s-n {n} {.n} (le-n .(succ n)) = le-n n
≤-s-n {n} {m} (le-s p)          = ≤-trans (le-s (le-n n)) p

≤-0-n : (n : ℕ) → 0 ≤ n
≤-0-n zero     = le-n 0
≤-0-n (succ n) = le-s (≤-0-n n)

≤-anti : {n m : ℕ} → n ≤ m → m ≤ n → n ≡ m
≤-anti {zero} {zero} p q     = refl _
≤-anti {succ n} {succ m} p q = ap succ (≤-anti (≤-s-n p) (≤-s-n q))

≤-s-0 : (n : ℕ) → ¬(succ n ≤ 0)
≤-s-0 n p = succ-not-0 n (≤-anti p (≤-0-n _))

{-
≤-total : ∀ (n m : ℕ) → (n ≤ m) ∨ (m ≤ n)
≤-total zero m            = left (≤-0-n m)
≤-total (succ n) zero     = right (≤-s-0 _)
≤-total (succ n) (succ m) with ≤-total n m
≤-total (succ n) (succ m) | left  p   = left (≤-n-s p)
≤-total (succ n) (succ m) | right p = right λ q → p (≤-s-n q)

max : ℕ → ℕ → ℕ
max = minmax.max _≤_ ≤-refl ≤-anti ≤-total 
-}

_<_ : ℕ → ℕ → Set
n < m = succ n ≤ m

infixr 4 _<_

<-n-s : {n m : ℕ} → n < m → succ n < succ m
<-n-s p = ≤-n-s p 

<-s-n : {n m : ℕ} -> succ n < succ m -> n < m
<-s-n p = ≤-s-n p

<-irrefl : {n : ℕ} → (n < n) -> 𝕆
<-irrefl {succ n} p = <-irrefl (<-s-n p) 

-- This is a weak result
<-trans : {n m p : ℕ} → n < m → m < p → n < p
<-trans {n} {m} {p} pnm qmp = ≤-trans pnm (≤-trans (le-s (le-n m)) qmp)

≤-transitive2 : transitive _≤_
≤-transitive2 = ≤-trans

ℕ-trichotomy : (n m : ℕ) → (n < m) ∨ (n ≡ m) ∨ (m < n)
ℕ-trichotomy zero zero      = left ( right (refl 0))
ℕ-trichotomy zero (succ m)  = left (left (≤-n-s (≤-0-n m)))
ℕ-trichotomy (succ n) zero  = right (≤-n-s (≤-0-n n))
ℕ-trichotomy (succ n) (succ m) with ℕ-trichotomy n m
ℕ-trichotomy (succ n) (succ m) | left (left p)  = left (left (≤-n-s p))
ℕ-trichotomy (succ n) (succ m) | left (right p) = left (right (ap succ p))
ℕ-trichotomy (succ n) (succ m) | right p        = right (≤-n-s p)

-- diffℕ n m = n - m
diffℕ : {n m : ℕ} → (m ≤ n) → ℕ
diffℕ {n} {zero} _        = n
diffℕ {succ n} {succ m} p = diffℕ (≤-s-n p)

diffℕ-pos : (n m : ℕ) -> (p : m ≤ n) -> (q : m < n) → diffℕ p ≡ succ (diffℕ q)
diffℕ-pos (succ n) zero p q     = refl (succ n)
diffℕ-pos (succ n) (succ m) p q = diffℕ-pos n m (≤-s-n p) (<-s-n q)
