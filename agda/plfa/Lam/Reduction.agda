module Lam.Reduction where

open import Data.Nat            using (ℕ;zero;suc;_+_;_*_)
open import Data.Bool           using (Bool;true;false)

open import Lam.Id
open import Lam.Op
open import Lam.Prim
open import Lam.Subst
open import Lam.Value
open import Lam.Syntax


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

  -- Reduction rule for primitive `+
  β-+ : ∀ {m n : ℕ}
        -------------------
    →  eOp `+ (eNum m) (eNum n) —→ eNum (m + n)

  -- Reduction rule for primitive `*
  β-* : ∀ {m n : ℕ}
        --------------------
    →  eOp `* (eNum m) (eNum n) —→ eNum (m * n)

  -- Reduction rule for primitive `=
  β-= : ∀ {m n : ℕ}
        ---------------------
    → eOp `= (eNum m) (eNum n) —→ eBool (m == n)

  -- Reduction rule for primitive `<
  β-< : ∀ {m n : ℕ}
        --------------------
    → eOp `< (eNum m) (eNum n) —→ eBool (m < n)

  -- Reduction rule for primitive `∧
  β-∧ : ∀ {x y : Bool}
        --------------------
    → eOp `∧ (eBool x) (eBool y) —→ eBool (and x y)

  -- Reduction rule for primitive `∨
  β-∨ : ∀ {x y : Bool}
        --------------------
    → eOp `∨ (eBool x) (eBool y) —→ eBool (or x y)

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

