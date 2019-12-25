module Lambda where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List using (List; _∷_; [])


Id : Set
Id = String

infix 5 ƛ_⇒_
infix 5 μ_⇒_
infixl 7 _∙_
infix 8 `suc_
infix 9 `_


data Term : Set where
  `_                   : Id → Term
  ƛ_⇒_                 : Id → Term → Term
  _∙_                  : Term → Term → Term
  `zero                : Term
  `suc_                : Term → Term
  case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term
  μ_⇒_                : Id → Term → Term


data Value : Term → Set where
  V-ƛ : {x : Id} → {N : Term} → Value (ƛ x ⇒ N)
  V-zero : Value `zero
  V-suc : {V : Term} → Value V → Value (`suc V)


infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` y) [ x := N ] = {!!}
(ƛ x₁ ⇒ M) [ x := N ] = {!!}
(M ∙ M₁) [ x := N ] = {!!}
`zero [ x := N ] = {!!}
(`suc M) [ x := N ] = {!!}
case M [zero⇒ M₁ |suc x₁ ⇒ M₂ ] [ x := N ] = {!!}
(μ x₁ ⇒ M) [ x := N ] = {!!}

