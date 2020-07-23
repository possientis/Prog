open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; subst;cong)

open import Data.String                                using (String; _≟_) -- \?=
open import Data.Nat                                   using (ℕ; zero; suc)
open import Data.Empty                                 using (⊥; ⊥-elim)
open import Relation.Nullary                           using (Dec; yes; no; ¬_)
open import Data.List                                  using (List; _∷_; [])
open import Data.Bool                                  using (Bool; true; false)
open import Data.Product                               using (∃; ∃-syntax; _×_)
open import Data.Product                               using () renaming (_,_ to ⟨_,_⟩)
open import isomorphism                                using (_≃_)

Id : Set
Id = String

data Op : Set where
  `+ : Op
  `* : Op
  `- : Op
  `/ : Op
  `= : Op
  `< : Op
  `∧ : Op
  `∨ : Op
  `→ : Op

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
sucᶜ = ƛ "n" ⇒ (`suc (` "n"))


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

  V-op : ∀ {op : Op} {V W : Term}
    → Value V
    → Value W
      --------------------
    → Value (eOp op V W)

  V-Num : ∀ {n : ℕ }
       --------------------
    →  Value (eNum n)

  V-Bool : ∀ {b : Bool}
       -------------------
    →  Value (eBool b)

  V-if : ∀ {V M N : Term}
    →   Value V
    →   ¬ V ≡ eBool true
    →   ¬ V ≡ eBool false
       --------------------
    →  Value (eIf V M N)

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

_ : (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) [ "x" := `zero ]
   ≡ ƛ "y" ⇒ `zero · (ƛ "x" ⇒ ` "x")
_ = refl

infix 4 _—→_ -- \em\to

-- Small-step operational semantics
-- Call-by-value: Subterms are reduced to values before the whole term is reduced
-- Left to right, hence deterministic, i.e. reduction is in fact functional.
data _—→_ : Term → Term → Set where

  -- Left compatibility rule for eOp
  ξ-op₁ : ∀ {op : Op} {L L' M : Term}
    →  L —→ L'
       --------------------
    →  eOp op L M —→ eOp op L' M

  -- Right compatibility rule for eOp
  ξ-op₂ : ∀ {op : Op} {V M M' : Term}
    →  Value V
    →  M —→ M'
       --------------------
    →  eOp op V M —→ eOp op V M'

  -- condition compatibility rule for eIf
  ξ-if₀ : ∀ {L L' M N : Term}
    →  L —→ L'
       --------------------
    →  eIf L M N —→ eIf L' M N

  -- If reduction on true
  β-if₁ : ∀ {M N : Term}
       --------------------
    →  eIf (eBool true) M N —→ M

  -- if reduction on false
  β-if₂ : ∀ {M N : Term}
       --------------------
    →  eIf (eBool false) M N —→ N

  -- Left compatibility rule for ·
  ξ-·₁ : ∀ {L L' M : Term}
    →  L —→ L'
       --------------------
    →  L · M —→ L' · M

  -- Right compatibility rule for ·
  ξ-·₂ : ∀ {V M M' : Term}
    →  Value V
    →  M —→ M'
       --------------------
    →  V · M —→ V · M'

  -- Beta reduction rule for abstraction
  β-ƛ : ∀ {x : Id} {N V : Term}
    → Value V
      --------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]


  -- Compatibility rule for suc
  ξ-suc : ∀ {M M' : Term}
    →  M —→ M'
      --------------------
    → (`suc M) —→ (`suc M')

  -- Compatibility rule for case
  ξ-case : ∀ {x : Id} {L L' M N : Term}
    →  L —→ L'
      --------------------
    →  case L [zero⇒ M |suc x ⇒ N ] —→ case L' [zero⇒ M |suc x ⇒ N ]


  -- Beta reduction rule for case (zero)
  β-zero : ∀ {x : Id} {M N : Term}
      --------------------
    →  case `zero [zero⇒ M |suc x ⇒ N ] —→ M


  -- Beta reduction rule for case (suc)
  β-suc : ∀ {x : Id} {V M N : Term}
    →  Value V
      --------------------
    →  case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  -- Beta reduction rule for fixed point
  -- The term being substituted is not a value
  -- Question: when is the substitution beta-valid ?
  β-μ : ∀ {x : Id} {M : Term}
      --------------------
    →  μ x ⇒ M —→ M [ x := μ x ⇒ M ]


L1 : (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") —→ ƛ "x" ⇒ ` "x"
L1 = β-ƛ V-ƛ


L2 : (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")
  —→ (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")
L2 = ξ-·₁ L1


infix 2 _—↠_ -- \em\rr-
infix 1 begin_
infixr 2 _—→⟨_⟩_
infixr 2 _—→⟨⟩_
infix 3 _∎

-- reflexive and transitive closure of _—→_
data _—↠_ : Term → Term → Set where

  _∎ : ∀ (M : Term)
      ---------------
    → M —↠ M

  _—→⟨_⟩_ : ∀ (L : Term) {M N : Term}
    → L —→ M
    → M —↠ N
      ---------------
    → L —↠ N

_—→⟨⟩_ : ∀ (L : Term) {M : Term}
  → L —↠ M
    ----------
  → L —↠ M

L —→⟨⟩ p = p

begin_ : ∀ {M N : Term}
  → M —↠ N
    ----------
  → M —↠ N
begin M—↠N = M—↠N

data _—↠'_ : Term → Term → Set where

  step' : ∀ {M N : Term}
    → M —→ N
      ----------
    → M —↠' N

  refl' : ∀ {M : Term}
      ---------------
    →  M —↠' M

  trans' : ∀ {L M N : Term}
    → L —↠' M
    → M —↠' N
      ----------
    → L —↠' N

—↠-trans : ∀ {L M N : Term} → L —↠ M → M —↠ N → L —↠ N
—↠-trans (_ ∎) q = q
—↠-trans (_ —→⟨ s ⟩ p) q = _ —→⟨ s ⟩ —↠-trans p q

—↠Imply—↠' : ∀ {M N : Term} → M —↠ N → M —↠' N
—↠Imply—↠' (_ ∎) = refl'
—↠Imply—↠' (_ —→⟨ s ⟩ p) = trans' (step' s) (—↠Imply—↠' p)

—↠'Imply—↠ : ∀ {M N : Term} → M —↠' N → M —↠ N
—↠'Imply—↠ {M} {N} (step' s) = begin M —→⟨ s ⟩ N ∎
—↠'Imply—↠ refl' = _ ∎
—↠'Imply—↠ (trans' p q) = —↠-trans (—↠'Imply—↠ p) (—↠'Imply—↠ q)

-- Predicate for a deterministic relation on a
Deterministic : ∀ {a : Set} → (a → a → Set) → Set
Deterministic {a} r = ∀ (x y y' : a) → r x y → r x y' → y ≡ y'

-- Reflexive, transitive closure of a relation r on a
data Closure {a : Set} (r : a → a → Set) : a → a → Set where
  cloRefl   : ∀ {x : a} → Closure r x x
  cloStep  : ∀ {x y z : a} → r x y → Closure r y z → Closure r x z

-- The reflexive, transitive closure is indeed a transitive relation
ClosureTrans : ∀ {a : Set} {r : a → a → Set} {x y z : a} →
  Closure r x y → Closure r y z → Closure r x z
ClosureTrans cloRefl q = q
ClosureTrans (cloStep p q) r = cloStep p (ClosureTrans q r)

-- https://en.wikipedia.org/wiki/Abstract_rewriting_system

-- Predicate for a relation which has the 'confluence' property
Confluent : ∀ {a : Set} → (a → a → Set) → Set
Confluent {a} r = ∀ {x y z : a}
  → Closure r x y
  → Closure r x z
    ---------------------
  → ∃[ t ] (Closure r y t × Closure r z t)

-- Predicate for a relation which has the 'semi-confluence' property
-- This is equivalent to confluence, see below
Semi-Confluent : ∀ {a : Set} → (a → a → Set) → Set
Semi-Confluent {a} r = ∀ {x y z : a}
  → r x y
  → Closure r x z
    ---------------------
  → ∃[ t ] (Closure r y t × Closure r z t)

-- Predicate for relation which has the 'diamond' property
-- aka 'locally confluent'
Diamond : ∀ {a : Set} → (a → a → Set) → Set
Diamond {a} r = ∀ (x y z : a)
  → r x y
  → r x z
    --------------------
  → ∃[ t ] (Closure r y t × Closure r z t)

Confluent→Semi-Confluent : ∀ {a : Set} → {r : a → a → Set} →
  Confluent r → Semi-Confluent r
Confluent→Semi-Confluent {a} {r} p r1 r2 with p (cloStep r1 cloRefl) r2
... | q = q

Semi-Confluent→Confluent : ∀ {a : Set} → {r : a → a → Set} →
  Semi-Confluent r → Confluent r
Semi-Confluent→Confluent {a} {r} p {z = z} cloRefl q2 = ⟨ z ,  ⟨ q2 , cloRefl ⟩ ⟩
Semi-Confluent→Confluent {a} {r} p (cloStep q q1) q2 with p q q2
... | ⟨ u , ⟨ r1 , r2 ⟩ ⟩ with Semi-Confluent→Confluent p q1 r1
... | ⟨ v , ⟨ s1 , s2 ⟩ ⟩ = ⟨ v , ⟨ s1 , ClosureTrans r2 s2 ⟩ ⟩

-- A Deterministic relation has the diamond property
Deterministic→Diamond : ∀ {a : Set} {r : a → a → Set} → Deterministic r → Diamond r
Deterministic→Diamond {a} {r} p x y z H1 H2
  = ⟨ y , ⟨ cloRefl , subst (Closure r z) (p x z y H2 H1) cloRefl ⟩ ⟩

-- The reflexive transitive closure of relation with diamond property is semi-confluent
Deterministic-Semi-Confluent : ∀ {a : Set} {r : a → a → Set} →
  Deterministic r → Semi-Confluent r
Deterministic-Semi-Confluent {a} {r} p {y = y} r1 cloRefl
  = ⟨ y , ⟨ cloRefl , cloStep r1 cloRefl ⟩ ⟩
Deterministic-Semi-Confluent {a} {r} p r1 (cloStep r2 r2') with p _ _ _ r1 r2
Deterministic-Semi-Confluent {a} {r} p {z = z} r1 (cloStep r2 r2') | refl
  = ⟨ z , ⟨ r2' , cloRefl ⟩  ⟩

-- The reflexive transitive closure of relation with diamond property is confluent
Deterministic-Confluent : ∀ {a : Set} {r : a → a → Set} →
  Deterministic r → Confluent r
Deterministic-Confluent p = Semi-Confluent→Confluent (Deterministic-Semi-Confluent p)

_ : twoᶜ · sucᶜ · `zero —↠ `suc `suc `zero
_ = begin
  twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
  (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
  sucᶜ · (sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
  sucᶜ · (`suc `zero)
  —→⟨ β-ƛ (V-suc V-zero) ⟩
  `suc (`suc `zero)
  ∎

_ : plus · two · two —↠ `suc `suc `suc `suc `zero
_ = begin
  plus · two · two

  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒ case ` "m"
      [zero⇒ ` "n"
      |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
  · two
  · two

  —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ "n" ⇒ case two
      [zero⇒ ` "n"
      |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
  · two

  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    case two
      [zero⇒ two
      |suc "m" ⇒ `suc (plus · ` "m" · two) ]

  —→⟨ β-suc (V-suc V-zero) ⟩
    `suc (plus · (`suc `zero) · two)

  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
  `suc
    ( (ƛ "m" ⇒ ƛ "n" ⇒ case ` "m"
        [zero⇒ ` "n"
        |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
    · (`suc `zero)
    · two)

  —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
  `suc
    ( (ƛ "n" ⇒ case `suc `zero
        [zero⇒ ` "n"
        |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
    · two)

  —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
  `suc (case `suc `zero
    [zero⇒ two
    |suc "m" ⇒ `suc (plus · ` "m" · two)] )

  —→⟨ ξ-suc (β-suc V-zero) ⟩
  `suc (`suc (plus · `zero · two))

  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
  `suc (`suc
    ( (ƛ "m" ⇒ ƛ "n" ⇒ case ` "m"
        [zero⇒ ` "n"
        |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
    · `zero · two))

  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
  `suc (`suc
    (  (ƛ "n" ⇒ case `zero
         [zero⇒ ` "n"
         |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
    · two))

  —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
  `suc (`suc
    case `zero
      [zero⇒ two
      |suc "m" ⇒ `suc (plus · `"m" · two) ])

  —→⟨ ξ-suc (ξ-suc β-zero) ⟩
  `suc (`suc two)

  —→⟨⟩
  `suc (`suc (`suc (`suc `zero)))
  ∎

_ : plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero —↠ `suc `suc `suc `suc `zero
_ = begin
  plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero

  —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    (ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · ` "s" · (` "n" · ` "s" · ` "z"))
  · twoᶜ
  · sucᶜ
  · `zero

  —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · ` "s" · (twoᶜ · ` "s" · ` "z"))
  · sucᶜ
  · `zero

  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ twoᶜ · sucᶜ · (twoᶜ · sucᶜ · ` "z"))
  · `zero

  —→⟨ β-ƛ V-zero ⟩
  twoᶜ · sucᶜ · (twoᶜ · sucᶜ · `zero)

  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z") )
  · (twoᶜ · sucᶜ · `zero)

  —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z"))
  · ((ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero)

  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z"))
  · (sucᶜ · (sucᶜ · `zero))

  —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z"))
  · (sucᶜ · (`suc `zero))

  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z"))
  · (`suc `suc `zero)

  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
  sucᶜ · (sucᶜ · (`suc `suc `zero))

  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
  sucᶜ · (`suc `suc `suc `zero)

  —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
  `suc `suc `suc `suc `zero
  ∎

_ : plus · (`suc `zero) · (`suc `zero) —↠ `suc `suc `zero
_ = begin
  plus · (`suc `zero) · (`suc `zero)

  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒ case ` "m"
      [zero⇒ ` "n"
      |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
  · (`suc `zero)
  · (`suc `zero)

  —→⟨ ξ-·₁ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "n" ⇒ case (`suc `zero)
      [zero⇒ ` "n"
      |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
  · (`suc `zero)

  —→⟨ β-ƛ (V-suc V-zero) ⟩
  case (`suc `zero)
    [zero⇒ (`suc `zero)
    |suc "m" ⇒ `suc (plus · ` "m" · (`suc `zero)) ]

  —→⟨ β-suc V-zero ⟩
  `suc (plus · `zero · (`suc `zero))

  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
  `suc (
      (ƛ "m" ⇒ ƛ "n" ⇒ case ` "m"
        [zero⇒ ` "n"
        |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
    · `zero
    · (`suc `zero))

  —→⟨ ξ-suc (ξ-·₁ (β-ƛ V-zero)) ⟩
  `suc (
      (ƛ "n" ⇒ case `zero
        [zero⇒ ` "n"
        |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
    · (`suc `zero))

  —→⟨ ξ-suc (β-ƛ (V-suc V-zero)) ⟩
  `suc case `zero
    [zero⇒ (`suc `zero)
    |suc "m" ⇒ `suc (plus · ` "m" · (`suc `zero)) ]

  —→⟨ ξ-suc β-zero ⟩
  `suc `suc `zero
  ∎


infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type -> Type -> Type
  `ℕ  : Type
  `𝔹  : Type


infixl 5 _,_∶_  -- \:

data Context : Set where
  ∅     : Context -- \0
  _,_∶_ : Context → Id → Type → Context


open _≃_

ContextListIso : Context ≃ List (Id × Type)
ContextListIso = record
  { to = toList
  ; from = fromList
  ; from∘to = fromTo
  ; to∘from = toFrom
  }
    where
      toList : Context → List (Id × Type)
      toList ∅ = []
      toList (Γ , x ∶ A) = ⟨ x , A ⟩ ∷ toList Γ
      fromList : List (Id × Type) → Context
      fromList [] = ∅
      fromList (⟨ x , A ⟩ ∷ xs) = fromList xs , x ∶ A
      fromTo : ∀ (Γ : Context) → fromList (toList Γ) ≡ Γ
      fromTo ∅ = refl
      fromTo (Γ , x ∶ A) = cong (_, x ∶ A) (fromTo Γ)
      toFrom : ∀ (xs : List (Id × Type)) → toList (fromList xs) ≡ xs
      toFrom [] = refl
      toFrom (⟨ x , A ⟩ ∷ xs) = cong (⟨ x , A ⟩ ∷_) (toFrom xs)

