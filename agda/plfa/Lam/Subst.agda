module Lam.Subst where

open import Data.String         using (_≟_) -- \?=
open import Relation.Nullary    using (Dec; yes; no; ¬_)

open import Lam.Id
open import Lam.Op
open import Lam.Syntax


infix 9 _[_:=_]

-- Substituting a single variable y with a term V (usually a value)
-- The term V had better be closed or we have a beta-validity issue
-- V will not be a value when dealing with a fixed point.
_[_:=_] : Term → Id → Term → Term

-- Integers
(eNum n) [ y := V ] = eNum n

-- Booleans
(eBool b) [ y := V ] = eBool b

-- Variable
(` x) [ y := V ] with x ≟ y
... | yes _ = V
... | no  _ = ` x

-- Op
(eOp op L M) [ y := V ] = eOp op (L [ y := V ]) (M [ y := V ])

-- If
(eIf B L M) [ y := V ] = eIf (B [ y := V ]) (L [ y := V ]) (M [ y := V ])

-- Lambda abstraction
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = ƛ x ⇒ N
... | no  _ = ƛ x ⇒ N [ y := V ]

-- Application
(L · M) [ y := V ] = L [ y := V ] · M [ y := V ]

-- Constant zero
`zero [ y := V ] = `zero

-- Successor
(`suc M) [ y := V ] = `suc (M [ y := V ])

-- Match
case L [zero⇒ M |suc x ⇒ N ] [ y := V ] with x ≟ y
... | yes _ = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _ = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]

-- Mu abstraction
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = μ x ⇒ N
... | no  _ = μ x ⇒ N [ y := V ]
