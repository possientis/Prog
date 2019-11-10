module vcombinator where

open import id
open import nat
open import sum
open import void

-- This language has variables but no binders
data VComb : Set where
    S   : VComb
    K   : VComb
    App : VComb → VComb → VComb
    Var : ℕ → VComb

-- With small-step semantics consistent with that of K S combinators
data _≻_ : VComb → VComb → Set where  -- /succ
    ≻K     : (a b : VComb)   → App (App K a) b ≻ a
    ≻S     : (a b c : VComb) → App (App (App S a) b) c ≻ App (App a c) (App b c)
    Cong1  : {a a' : VComb}  →  (b : VComb) → a ≻ a' → App a b ≻ App a' b
    Cong2  : {b b' : VComb}  →  (a : VComb) → b ≻ b' → App a b ≻ App a  b'


-- transitive closure of ≻
data _≽_ : VComb -> VComb -> Set where -- /succeq
  ≽Refl  : {a b   : VComb} → a ≻ b → a ≽ b
  ≽Trans : {a b c : VComb} → a ≻ b → b ≽ c → a ≽ c

-- We are able create 'functional' bindings without binding syntax
λ* : ℕ → VComb → VComb
λ* n S = App K S
λ* n K = App K K
λ* n (App c₁ c₂) = App (App S (λ* n c₁)) (λ* n c₂)
λ* n (Var m) with eq-dec n m
λ* n (Var m) | left  p = App (App S K) K
λ* n (Var m) | right p = App K (Var m)

data IsVarOf : ℕ → VComb → Set where
  LeftApp  : {n : ℕ} → {c₁ : VComb} → (c₂ : VComb) → IsVarOf n c₁ →
    IsVarOf n (App c₁ c₂)
  RightApp : {n : ℕ} → {c₂ : VComb} → (c₁ : VComb) → IsVarOf n c₂ →
    IsVarOf n (App c₁ c₂)
  VarIs : (n : ℕ) → IsVarOf n (Var n)

-- Such functional bindings remove the 'bound' variable from the formula
λ*-binds : ∀ (n : ℕ) (c : VComb) → ¬ IsVarOf n (λ* n c)
λ*-binds n S (LeftApp  .S ())
λ*-binds n S (RightApp .K ())
λ*-binds n K (LeftApp  .K ())
λ*-binds n K (RightApp .K ())
λ*-binds n (App c₁ c₂) (LeftApp .(λ* n c₂) (RightApp .S p)) = λ*-binds n c₁ p
λ*-binds n (App c₁ c₂) (RightApp .(App S (λ* n c₁)) p) = λ*-binds n c₂ p
λ*-binds n (Var m) p with eq-dec n m
λ*-binds n (Var m) (LeftApp .K (LeftApp .K ())) | left q
λ*-binds n (Var m) (LeftApp .K (RightApp .S ())) | left q
λ*-binds n (Var .n) (RightApp .K (VarIs .n)) | right q = q (refl _)

-- A syntax with no binders hugely simplifies the notion of variable β-substitution
-- Replacing variable 'n' with term 'c'
[_/_] : VComb → ℕ → VComb → VComb
[ c / n ] S = S
[ c / n ] K = K
[ c / n ] (App c₁ c₂) = App ([ c / n ] c₁) ([ c / n ] c₂)
[ c / n ] (Var m) with eq-dec n m
[ c / n ] (Var m) | left  p = c
[ c / n ] (Var m) | right p = Var m

-- A few convenient lemmas
≽-Cong1 : ∀ {a a' : VComb} → (b : VComb) → a ≽ a' → App a b ≽ App a' b
≽-Cong1 b (≽Refl p) = ≽Refl (Cong1 _ p)
≽-Cong1 b (≽Trans p q) = ≽Trans (Cong1 _ p) (≽-Cong1 b q)

≽-Cong2 : ∀ {b b' : VComb} → (a : VComb) → b ≽ b' → App a b ≽ App a b'
≽-Cong2 a (≽Refl p) = ≽Refl (Cong2 _ p)
≽-Cong2 a (≽Trans p q) = ≽Trans (Cong2 _ p) (≽-Cong2 _ q)

-- More convenient than constructor ≽Trans
≽-Trans : {a b c : VComb} → a ≽ b → b ≽ c → a ≽ c
≽-Trans (≽Refl p) q = ≽Trans p q
≽-Trans (≽Trans p q) r = ≽Trans p (≽-Trans q r)

-- This is the key : 'functional' binding does emulate β-reduction
λ*-≽ : ∀ (c₁ c₂ : VComb) (n : ℕ) → App (λ* n c₁) c₂ ≽ [ c₂ / n ] c₁
λ*-≽ S c₂ n = ≽Refl (≻K _ _)
λ*-≽ K c₂ n = ≽Refl (≻K _ _)
λ*-≽ (App c c₁) c₂ n = ≽Trans (≻S _ _ _)
  (≽-Trans (≽-Cong1 _ (λ*-≽ c c₂ n))
  (≽-Cong2 _ (λ*-≽ c₁ c₂ n)))
λ*-≽ (Var m) c₂ n with eq-dec n m
λ*-≽ (Var m) c₂ n | left  p = ≽Trans (≻S _ _ _) (≽Refl (≻K _ _))
λ*-≽ (Var m) c₂ n | right p = ≽Refl (≻K _ _)

