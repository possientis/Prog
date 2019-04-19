module bool where

data 𝔹 : Set where
  tt : 𝔹
  ff : 𝔹

{-# BUILTIN BOOL 𝔹 #-}
{-# BUILTIN TRUE tt #-}
{-# BUILTIN FALSE ff #-}

infix 7 ¬_

¬_ : 𝔹 → 𝔹
¬ tt = ff
¬ ff = tt

infixr 6 _&&_

_&&_ : 𝔹 → 𝔹 → 𝔹
tt && y = y
ff && y = ff

infixr 5 _||_

_||_ : 𝔹 → 𝔹 → 𝔹
tt || y = tt
ff || y = y

if_then_else_ : ∀ {ℓ} {a : Set ℓ} → 𝔹 → a → a → a
if tt then x else y = x
if ff then x else y = y


