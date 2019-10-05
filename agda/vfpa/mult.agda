module mult where

open import id
open import nat
open import plus

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
