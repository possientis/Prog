module Lam.Prim where

open import Data.Nat            using (ℕ;zero;suc)
open import Data.Bool           using (Bool;true;false)

_==_ : ℕ → ℕ → Bool
zero == zero = true
zero == suc n = false
suc m == zero = false
suc m == suc n = m == n

_<_ : ℕ → ℕ → Bool
zero < zero = false
zero < suc n = true
suc m < zero = false
suc m < suc n = m < n

and : Bool → Bool → Bool
and false false = false
and false true = false
and true false = false
and true true = true

or : Bool → Bool → Bool
or false false = false
or false true = true
or true false = true
or true true = true
