module combinator where

open import nat
open import bool
open import min-max

data Comb : Set where
  S   : Comb
  K   : Comb
  App : Comb → Comb → Comb

data _≻_ : Comb → Comb → Set where
  ≻K     : (a b : Comb)   → App (App K a) b ≻ a
  ≻S     : (a b c : Comb) → App (App (App S a) b) c ≻ App (App a c) (App b c)
  Cong1  : {a a' : Comb}  →  (b : Comb) → a ≻ a' → App a b ≻ App a' b
  Cong2  : {b b' : Comb}  →  (a : Comb) → b ≻ b' → App a b ≻ App a  b'

{-
size : Comb → ℕ
size S           = 0
size K           = 0
size (App c₁ c₂) = max 1 2
-}




