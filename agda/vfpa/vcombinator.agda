module vcombinator where

open import id
open import nat
open import sum
open import void

data VComb : Set where
    S   : VComb
    K   : VComb
    App : VComb → VComb → VComb
    Var : ℕ → VComb


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

[_/_] : VComb → ℕ → VComb → VComb
[ c / n ] S = S
[ c / n ] K = K
[ c / n ] (App c₁ c₂) = App ([ c / n ] c₁) ([ c / n ] c₂)
[ c / n ] (Var m) with eq-dec n m
[ c / n ] (Var m) | left  p = c
[ c / n ] (Var m) | right p = Var m
