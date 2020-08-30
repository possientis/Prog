module Lam.Syntax where

open import Data.Nat
open import Data.Bool

open import Lam.Id
open import Lam.Op

infix 5 ƛ_⇒_
infix 5 μ_⇒_
infixl 7 _·_
infix 8 `suc_
infix 9 `_

data Term : Set where
  eNum                 : ℕ → Term
  eBool                : Bool → Term
  `_                   : Id → Term
  eOp                  : Op → Term → Term → Term
  eIf                  : Term → Term → Term → Term
  ƛ_⇒_                 : Id → Term → Term
  _·_                  : Term → Term → Term
  `zero                : Term
  `suc_                : Term → Term
  case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term
  μ_⇒_                 : Id → Term → Term



