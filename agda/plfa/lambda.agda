open import Relation.Binary.PropositionalEquality.Core using (_≡_;_≢_;refl)
open import Data.String                                using (String)
open import Data.Nat                                   using (ℕ; zero; suc)
open import Data.Empty                                 using (⊥; ⊥-elim)
open import Relation.Nullary                           using (Dec; yes; no; ¬_)
open import Data.List                                  using (List; _∷_; [])

Id : Set
Id = String

infix 5 ƛ_⇒_
infix 5 μ_⇒_
infixl 7 _·_
infix 8 `suc_
infix 9 `_

data Term : Set where
  `_                   : Id → Term
  ƛ_⇒_                 : Id → Term → Term
  _·_                  : Term → Term → Term
  `zero                : Term
  `suc_                : Term → Term
  case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term
  μ_⇒_                 : Id → Term → Term

two : Term
two = `suc (`suc `zero)

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
  case ` "m"
     [zero⇒ ` "n"
     |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
     ]
