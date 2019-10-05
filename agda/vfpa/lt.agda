module lt where

open import le
open import nat
open import void


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

