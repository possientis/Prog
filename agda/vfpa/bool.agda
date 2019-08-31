module bool where

open import id
open import sum
open import void


data 𝔹 : Set where
  tt : 𝔹
  ff : 𝔹

{-# BUILTIN BOOL 𝔹 #-}
{-# BUILTIN TRUE tt #-}
{-# BUILTIN FALSE ff #-}

infixr 6 _&&_

_&&_ : 𝔹 → 𝔹 → 𝔹
tt && y = y
ff && y = ff

infixr 5 _||_

_||_ : 𝔹 → 𝔹 → 𝔹
tt || y = tt
ff || y = y

not : 𝔹 → 𝔹
not tt = ff
not ff = tt

if_then_else_ : ∀ {ℓ} {a : Set ℓ} → 𝔹 → a → a → a
if tt then x else y = x
if ff then x else y = y

&&-diag : {b : 𝔹} → b && b ≡ b
&&-diag {tt} = refl _
&&-diag {ff} = refl _

||-is-false : {b1 b2 : 𝔹} → b1 || b2 ≡ ff → b1 ≡ ff
||-is-false {ff} {ff} p = refl ff

if-then-else-same : ∀ {ℓ} {X : Set ℓ} (x : X) (b : 𝔹) → if b then x else x ≡ x
if-then-else-same x tt = refl x
if-then-else-same x ff = refl x

𝔹-contra : ff ≡ tt → 𝕆
𝔹-contra ()

𝔹-contra' : ∀ {ℓ} → ff ≡ tt → {P : Set ℓ} → P
𝔹-contra' ()

&&-left : ∀ (b1 b2 : 𝔹) → b1 && b2 ≡ tt → b1 ≡ tt
&&-left tt _ _ = refl _

&&-right : ∀ (b1 b2 : 𝔹) → b1 && b2 ≡ tt → b2 ≡ tt
&&-right tt _ p = p

&&-and : ∀ {b1 b2 : 𝔹} → b1 ≡ tt → b2 ≡ tt → b1 && b2 ≡ tt
&&-and (refl _) (refl _) = refl _

𝔹-dec : eq_decidable 𝔹
𝔹-dec tt tt = left (refl _)
𝔹-dec tt ff = right λ p → 𝔹-contra (≡-sym p)
𝔹-dec ff tt = right 𝔹-contra
𝔹-dec ff ff = left (refl _)

