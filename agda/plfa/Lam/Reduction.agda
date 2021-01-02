module Lam.Reduction where

open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; sym; cong)

open import Data.Empty          using (⊥; ⊥-elim)
open import Data.Nat            using (ℕ;zero;suc;_+_;_*_)
open import Data.Bool           using (Bool;true;false)

open import Lam.Id
open import Lam.Op
open import Lam.Cong
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

  -- eIf reduction on true
  β-if₁ : ∀ {M N : Term}
       --------------------
    →  eIf (eBool true) M N —→ M

  -- eIf reduction on false
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


valueReduce : ∀ {M N : Term} → Value M → M —→ N → ⊥
valueReduce (V-suc p) (ξ-suc q) = valueReduce p q

det : ∀ {M N N' : Term}
  → M —→ N
  → M —→ N'
    ----------
  → N ≡ N'

det (ξ-op₁ p) (ξ-op₁ q) = cong _ (det p q)
det (ξ-op₁ p) (ξ-op₂ v q) = ⊥-elim (valueReduce v p)
det (ξ-op₂ v p) (ξ-op₁ q) = ⊥-elim (valueReduce v q)
det (ξ-op₂ v p) (ξ-op₂ x q) = cong _ (det p q)
det β-+ β-+ = refl
det β-* β-* = refl
det β-= β-= = refl
det β-< β-< = refl
det β-∧ β-∧ = refl
det β-∨ β-∨ = refl
det (ξ-if₀ p) (ξ-if₀ q) = cong _ (det p q)
det β-if₁ β-if₁ = refl
det β-if₂ β-if₂ = refl
det (ξ-·₁ p) (ξ-·₁ q) = cong _ (det p q)
det (ξ-·₁ p) (ξ-·₂ v q) = ⊥-elim (valueReduce v p)
det (ξ-·₂ v p) (ξ-·₁ q) = ⊥-elim (valueReduce v q)
det (ξ-·₂ v p) (ξ-·₂ w q) = cong _ (det p q)
det (ξ-·₂ v p) (β-ƛ w) = ⊥-elim (valueReduce w p)
det (β-ƛ v) (ξ-·₂ w q) = ⊥-elim (valueReduce v q)
det (β-ƛ v) (β-ƛ w) = refl
det (ξ-suc p) (ξ-suc q) = cong _ (det p q)
det (ξ-case p) (ξ-case q) = cong _ (det p q)
det (ξ-case p) (β-suc v) = ⊥-elim (valueReduce (V-suc v) p)
det β-zero β-zero = refl
det (β-suc v) (ξ-case q) = ⊥-elim (valueReduce (V-suc v) q)
det (β-suc v) (β-suc w) = refl
det β-μ β-μ = refl
