module Lam.Type where

infixr 7 _⇒_

data Type : Set where
  _⇒_  : Type -> Type -> Type
  `ℕ   : Type
  `𝔹   : Type
  `Num : Type



