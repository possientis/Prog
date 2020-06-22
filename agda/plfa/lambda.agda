open import Relation.Binary.PropositionalEquality.Core using (_≡_;_≢_;refl)
open import Data.String                                using (String; _≟_) -- \?=
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

twoᶜ : Term -- Church encoding
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
  ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term -- Not Church here
sucᶜ = ƛ "n" ⇒ `suc ` "n"


mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
  case ` "m"
    [zero⇒ `zero
    |suc "m" ⇒ plus · ` "n" · (` "*" · ` "m" · ` "n")
    ]

mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
  ` "m" · (` "n" · ` "s") · ` "z"

error : ∀ {a : Set} → a
error = ⊥-elim impossible
  where postulate impossible : ⊥

ƛ'_⇒_ : Term → Term → Term
ƛ' (` x) ⇒ N = ƛ x ⇒ N
ƛ' _ ⇒ _ = error

case'_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case' L [zero⇒ M |suc ` x ⇒ N ] = case L [zero⇒ M |suc x ⇒ N ]
case' L [zero⇒ M |suc _ ⇒ N ] = error

μ'_⇒_ : Term → Term → Term
μ' ` x ⇒ N = μ x ⇒ N
μ' _ ⇒ N = error

test : Term
test = ƛ' two ⇒ two

plus' : Term
plus' = μ' + ⇒ ƛ' m ⇒ ƛ' n ⇒
  case' m
    [zero⇒ n
    |suc m ⇒ `suc (+ · m · n)
    ]
  where
  + = ` "+"
  m = ` "m"
  n = ` "n"

data Value : Term -> Set where

  V-ƛ : ∀ {x : Id} {N : Term}
      -----------------------
    → Value (ƛ x ⇒ N)

  V-zero :
      -----------------------
      Value `zero

  V-suc : ∀ {V : Term}
    → Value V
      -----------------------
    → Value (`suc V)

infix 9 _[_:=_]

-- Substituting a single variable y by a term V (usually a value)
-- The term V had better be closed or we have beta-validity issue
_[_:=_] : Term → Id → Term → Term

-- Variable
(` x) [ y := V ] with x ≟ y
... | yes _ = V
... | no  _ = ` x

-- Lambda abstraction
(ƛ x ⇒ N) [ y := V ] with x ≟ y 
... | yes _ = ƛ x ⇒ N
... | no  _ = ƛ x ⇒ N [ y := V ]

-- Application
(L · M) [ y := V ] = L [ y := V ] · M [ y := V ]

-- Constant zero
`zero [ y := V ] = `zero

-- Successor
(`suc M) [ y := V ] = `suc M [ y := V ]

-- Match
case L [zero⇒ M |suc x ⇒ N ] [ y := V ] with x ≟ y
... | yes _ = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _ = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]

-- Mu abstraction
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = μ x ⇒ N
... | no  _ = μ x ⇒ N [ y := V ]

_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] ≡ sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ] ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ ` "y"
_ = refl

_ : (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) [ "x" := `zero ] ≡ ƛ "y" ⇒ `zero · (ƛ "x" ⇒ ` "x")
_ = refl
