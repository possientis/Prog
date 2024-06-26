open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; subst;cong)

open import Data.Nat                                   using (ℕ;zero;suc;_≤_;s≤s;z≤n;_+_;_*_)
open import Data.Empty                                 using (⊥; ⊥-elim)
open import Relation.Nullary                           using (Dec; yes; no; ¬_)
open import Data.List                                  using (List; _∷_; [])
open import Data.Product                               using (∃; ∃-syntax; _×_)
open import Data.Product                               using () renaming (_,_ to ⟨_,_⟩)
open import isomorphism                                using (_≃_)
open import decidable                                  using (T;toWitness;⌞_⌟;_≤?_)

open import Lam.Id
open import Lam.Type
open import Lam.Subst
open import Lam.Value
open import Lam.Syntax
open import Lam.Typing
open import Lam.Closure
open import Lam.Context
open import Lam.Reduction

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

L1 : (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") —→ ƛ "x" ⇒ ` "x"
L1 = β-ƛ V-ƛ


L2 : (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")
  —→ (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")
L2 = ξ-·₁ L1

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

_ : ∅ , "x" ∶  `ℕ ⇒ `ℕ , "y" ∶ `ℕ , "z" ∶ `ℕ   ∋   "x" ∶  `ℕ ⇒ `ℕ
_ = S (λ ()) (S (λ ()) Z)

-- Refresher on reflection
minus : (m n : ℕ) → (n≤m : n ≤ m) → ℕ
minus m zero _ = m
minus (suc m) (suc n) (s≤s n≤m) = minus m n n≤m

_ : minus 5 3 (s≤s (s≤s (s≤s z≤n))) ≡ 2
_ = refl

_-_ : (m n : ℕ) → {n≤m : T ⌞ n ≤? m ⌟} → ℕ
_-_ m n {n≤m} = minus m n (toWitness n≤m)

_ : 5 - 3 ≡ 2
_ = refl

_ : ∅ , "x" ∶  `ℕ ⇒ `ℕ , "y" ∶ `ℕ , "z" ∶ `ℕ   ∋   "x" ∶  `ℕ ⇒ `ℕ
_ = S' (S' Z)

Church : Type -> Type
Church A = (A ⇒ A) ⇒ A ⇒ A

⊢twoᶜ : ∀ {Γ : Context} {A : Type} → Γ ⊢ twoᶜ ∶ Church A
⊢twoᶜ = ⊢ƛ (⊢ƛ (⊢· (⊢` (S (λ ()) Z)) (⊢· (⊢` (S (λ ()) Z)) (⊢` Z))))

⊢two : ∀ {Γ : Context} → Γ ⊢ two ∶ `ℕ
⊢two = ⊢suc (⊢suc ⊢zero)

⊢plus : ∀ {Γ : Context} → Γ ⊢ plus ∶ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` (S (λ ()) Z)) (⊢` Z)
  (⊢suc (⊢· (⊢· (⊢` (S (λ()) (S (λ()) (S (λ()) Z)))) (⊢` Z)) (⊢` (S (λ()) Z)))))))

⊢2+2 : ∀ {Γ : Context} → Γ ⊢ plus · two · two ∶ `ℕ
⊢2+2 = ⊢· (⊢· ⊢plus ⊢two) ⊢two

⊢plusᶜ : ∀ {Γ : Context} {A : Type} → Γ ⊢ plusᶜ ∶ Church A ⇒ Church A ⇒ Church A
⊢plusᶜ = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ (⊢·
  (⊢· (⊢` (S' (S' (S' Z)))) (⊢` (S' Z)))
  (⊢· (⊢· (⊢` (S' (S' Z))) (⊢` (S' Z))) (⊢` Z))))))

⊢sucᶜ : ∀ {Γ : Context} → Γ ⊢ sucᶜ ∶ `ℕ ⇒ `ℕ
⊢sucᶜ = ⊢ƛ (⊢suc (⊢` Z))

⊢2+2ᶜ : ∀ {Γ : Context} → Γ ⊢ plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero ∶ `ℕ
⊢2+2ᶜ = ⊢· (⊢· (⊢· (⊢· ⊢plusᶜ ⊢twoᶜ) ⊢twoᶜ) ⊢sucᶜ) ⊢zero

∋-injective : ∀ {Γ : Context} {x : Id} {A B : Type} →
  Γ ∋ x ∶ A → Γ ∋ x ∶ B → A ≡ B
∋-injective Z Z = refl
∋-injective Z (S p q) = ⊥-elim (p refl)
∋-injective (S p q) Z = ⊥-elim (p refl)
∋-injective (S p q) (S r s) = ∋-injective q s

nope₁ : ∀ {Γ : Context} {A : Type} {M : Term} → ¬ (Γ ⊢ `zero · M ∶ A)
nope₁ (⊢· () q)

nope₂ : ∀ {Γ : Context} {A : Type} → ¬ (Γ ⊢ ƛ "x" ⇒ ` "x" · ` "x" ∶ A)
nope₂ (⊢ƛ (⊢· (⊢` q) (⊢` p))) = contradiction (∋-injective p q)
  where
    contradiction : ∀ {A B : Type} → ¬ (A ≡ A ⇒ B)
    contradiction ()

ex₁ : ∀ {Γ : Context} → Γ , "y" ∶ `ℕ ⇒ `ℕ , "x" ∶ `ℕ ⊢ ` "y" · ` "x" ∶ `ℕ
ex₁ = ⊢· (⊢` (S' Z)) (⊢` Z)

ex₂ : ∀ {Γ : Context} {A : Type} →
  Γ , "y" ∶ `ℕ ⇒ `ℕ , "x" ∶ `ℕ ⊢ ` "y" · ` "x" ∶ A → A ≡ `ℕ
ex₂ (⊢· (⊢` (S _ Z)) (⊢` q)) = refl
ex₂ (⊢· (⊢` (S _ (S p q))) (⊢` Z)) = ⊥-elim (p refl)
ex₂ (⊢· (⊢` (S _ (S p q))) (⊢` (S r s))) = ⊥-elim (p refl)

ex₃ : ∀ {Γ : Context} {A : Type} →
  ¬(Γ , "y" ∶ `ℕ ⇒ `ℕ , "x" ∶ `ℕ ⊢ ` "x" · ` "y" ∶ A)
ex₃ (⊢· (⊢` (S p _)) _) = ⊥-elim (p refl)

ex₄ : ∀ {Γ : Context} →
  Γ , "y" ∶ `ℕ ⇒ `ℕ ⊢ ƛ "x" ⇒ ` "y" · ` "x" ∶ `ℕ ⇒ `ℕ
ex₄ = ⊢ƛ (⊢· (⊢` (S' Z)) (⊢` Z))

ex₅ : ∀ {Γ : Context} {A : Type} →
  Γ , "y" ∶ `ℕ ⇒ `ℕ ⊢ ƛ "x" ⇒ ` "y" · ` "x" ∶ A → A ≡ `ℕ ⇒ `ℕ
ex₅ (⊢ƛ (⊢· (⊢` (S _ Z)) (⊢` Z))) = refl
ex₅ (⊢ƛ (⊢· (⊢` (S _ (S p _))) (⊢` Z))) = ⊥-elim (p refl)
ex₅ (⊢ƛ (⊢· _ (⊢` (S p _)))) = ⊥-elim (p refl)

ex₆ : ∀ {Γ : Context} {A B : Type} → ¬(Γ , "x" ∶ A ⊢ ` "x" · ` "x" ∶ B)
ex₆ (⊢· (⊢` (S p _)) (⊢` Z)) = ⊥-elim (p refl)
ex₆ (⊢· _ (⊢` (S p _))) = ⊥-elim (p refl)

ex₇ : ∀ {Γ : Context} {A B C : Type} →
  Γ , "x" ∶ B ⇒ C , "y" ∶ A ⇒ B ⊢ ƛ "z" ⇒ ` "x" · (` "y" · ` "z") ∶ A ⇒ C
ex₇ = ⊢ƛ (⊢· (⊢` (S' (S' Z))) (⊢· (⊢` (S' Z)) (⊢` Z)))

⊢mul : ∀ {Γ : Context} → Γ ⊢  mul ∶ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢mul = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` (S' Z)) ⊢zero (⊢· (⊢· ⊢plus (⊢` (S' Z)))
  (⊢· (⊢· (⊢` (S' (S' (S' Z)))) (⊢` Z)) (⊢` (S' Z)))))))

⊢mulᶜ : ∀ {Γ : Context} {A : Type} → Γ ⊢ mulᶜ ∶ Church A ⇒ Church A ⇒ Church A
⊢mulᶜ = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ (⊢· (⊢· (⊢` (S' (S' (S' Z))))
  (⊢· (⊢` (S' (S' Z))) (⊢` (S' Z)))) (⊢` Z)))))
