module combinator where

open import le
open import le
open import lt
open import nat
open import bool
open import plus

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
order (App c₁ c₂) = succ (order c₁ + order c₂)

data SFree : Comb -> Set where
  SFreeK   : SFree K
  SFreeApp : {c₁ c₂ : Comb} → SFree c₁ → SFree c₂ → SFree (App c₁ c₂)

{-
-- If c reduces to c' and is SFree, then the order of c' is less than that of c
reduct-order : ∀ {c c' : Comb} → SFree c → c ≻ c' → order c' < order c
reduct-order (SFreeApp p₁ p₂) (≻K a b) = ≤-n-s (le-s (n-≤-n+m _ _))
reduct-order (SFreeApp (SFreeApp (SFreeApp () p₃) p₁) p₂) (≻S a b c) 
reduct-order (SFreeApp p₁ p₂) (Cong1 b q) = <-n-s ? 
reduct-order (SFreeApp p₁ p₂) (Cong2 a q) = {!!} 
-}




