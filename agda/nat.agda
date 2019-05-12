module nat where

open import id
open import bool

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero   + y = y
succ x + y = succ (x + y)

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

_<_ : ℕ → ℕ → 𝔹
0 < 0           = ff
succ _ < 0      = ff
0 < succ _      = tt
succ x < succ y = x < y

<-trans : {n m p : ℕ} → n < m ≡ tt → m < p ≡ tt → n < p ≡ tt
<-trans {zero} {succ m} {succ p} p1 p2   = refl tt
<-trans {succ n} {succ m} {succ p} p1 p2 = <-trans {n} {m} {p} p1 p2

<-0 : {n : ℕ} → n < 0 ≡ ff
<-0 {zero}   = refl ff
<-0 {succ n} = refl ff

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

even-not-odd : (n : ℕ) → is-even n ≡ ¬(is-odd n)
even-not-odd zero = refl tt
even-not-odd (succ n) = ≡-sym
  (≡-trans
    (ap ¬_ (even-not-odd n))
    (¬-involutive (is-odd n))) 

data _≤_ : ℕ → ℕ → Set where
  le-n : (n : ℕ)   → n ≤ n
  le-s : {n m : ℕ} → n ≤ m → n ≤ succ m 

infixr 4 _≤_

≤-refl : (n : ℕ) → n ≤ n
≤-refl n = le-n n

≤-trans : {n m p : ℕ} → n ≤ m → m ≤ p → n ≤ p
≤-trans p (le-n n) = p
≤-trans p (le-s q) = le-s (≤-trans p q)

le-n-s : {n m : ℕ} → n ≤ m → succ n ≤ succ m
le-n-s (le-n n) = le-n (succ n)
le-n-s (le-s p) = le-s (le-n-s p)

le-s-n : {n m : ℕ} → succ n ≤ succ m → n ≤ m
le-s-n {n} {.n} (le-n .(succ n)) = le-n n
le-s-n {n} {m} (le-s p) = ≤-trans (le-s (le-n n)) p
