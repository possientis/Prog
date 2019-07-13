module nat where

open import id    hiding (_+_)
open import bool
open import void
open import relations

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

_=ℕ_ : ℕ → ℕ → 𝔹
zero =ℕ zero     = tt
zero =ℕ succ m   = ff
succ n =ℕ zero   = ff
succ n =ℕ succ m = n =ℕ m

=ℕ-refl : (n : ℕ) → (n =ℕ n) ≡ tt
=ℕ-refl zero     = refl tt
=ℕ-refl (succ n) = =ℕ-refl n

=ℕ-sym : (n m : ℕ) → (n =ℕ m) ≡ tt → (m =ℕ n) ≡ tt
=ℕ-sym zero zero p         = refl tt
=ℕ-sym (succ n) (succ m) p = =ℕ-sym n m p

=ℕ-trans : (n m p : ℕ) → (n =ℕ m ≡ tt) → (m =ℕ p ≡ tt) → (n =ℕ p ≡ tt)
=ℕ-trans zero zero zero q_nm q_mp = refl tt
=ℕ-trans (succ n) (succ m) (succ p) q_nm q_mp = =ℕ-trans n m p q_nm q_mp

=ℕ-to-≡ : (n m : ℕ) → (n =ℕ m ≡ tt) → n ≡ m
=ℕ-to-≡ zero zero p = refl zero
=ℕ-to-≡ (succ n) (succ m) p = ap succ (=ℕ-to-≡ n m p)

=ℕ-from-≡ : (n m : ℕ) → (n ≡ m) → (n =ℕ m ≡ tt)
=ℕ-from-≡ n m p = ≡-trans (≡-sym (ap (λ x → n =ℕ x) p)) (=ℕ-refl n)

is-even : ℕ → 𝔹
is-odd  : ℕ → 𝔹
is-even zero = tt
is-even (succ n) = is-odd n
is-odd zero = ff
is-odd (succ n) = is-even n

data _≤_ : ℕ → ℕ → Set where
  le-n : (n : ℕ)   → n ≤ n
  le-s : {n m : ℕ} → n ≤ m → n ≤ succ m 

infixr 4 _≤_

_<_ : ℕ → ℕ → Set
n < m = succ n ≤ m

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

pred : (n : ℕ) → ℕ
pred zero     = 0
pred (succ n) = n

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
