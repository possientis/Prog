module combinator where

open import le
open import lt
open import nat
open import bool

data Comb : Set where
  S   : Comb
  K   : Comb
  App : Comb → Comb → Comb

data _≻_ : Comb → Comb → Set where  -- /succ    
  ≻K     : (a b : Comb)   → App (App K a) b ≻ a
  ≻S     : (a b c : Comb) → App (App (App S a) b) c ≻ App (App a c) (App b c)
  Cong1  : {a a' : Comb}  →  (b : Comb) → a ≻ a' → App a b ≻ App a' b
  Cong2  : {b b' : Comb}  →  (a : Comb) → b ≻ b' → App a b ≻ App a  b'


order : Comb → ℕ
order S           = 0
order K           = 0
order (App c₁ c₂) = succ (max (order c₁) (order c₂))

{-
reduct-order : ∀ {c c' : Comb} → c ≻ c' → order c' < order c
reduct-order (≻K a b)    = {!!}
reduct-order (≻S a b c)  = {!!}
reduct-order (Cong1 b p) = {!!}
reduct-order (Cong2 a p) = {!!}
-}




