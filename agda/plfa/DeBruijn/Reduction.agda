module DeBruijn.Reduction where

open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; sym; cong)

open import Data.Empty          using (⊥; ⊥-elim)
open import Data.Nat            using (ℕ; zero; suc; _+_; _*_)
open import Data.Bool           using (Bool;true;false)

open import Lam.Type
open import Lam.Prim
open import DeBruijn.Subst
open import DeBruijn.Value
open import DeBruijn.Syntax
open import DeBruijn.Context

infix 2 _—→_ -- \em\to

-- Reduction preserves type by construction
data _—→_ : ∀ {Γ : Context} {A : Type} → Γ ⊢ A → Γ ⊢ A → Set where

  -- Left compatibility rule for +
  ξ-+₁ : ∀ {Γ : Context} {L L' M : Γ ⊢ `Num}
    → L —→ L'
      -------------------------------------
    → `+ L M —→ `+ L' M


  -- Right compatibility rule for +
  ξ-+₂ : ∀ {Γ : Context} {V M M' : Γ ⊢ `Num}
    → Value V
    → M —→ M'
      ---------------------------------------
    → `+ V M —→ `+ V M'


  -- Left compatibility rule for *
  ξ-*₁ : ∀ {Γ : Context} {L L' M : Γ ⊢ `Num}
    → L —→ L'
      -------------------------------------
    → `* L M —→ `* L' M


  -- Right compatibility rule for *
  ξ-*₂ : ∀ {Γ : Context} {V M M' : Γ ⊢ `Num}
    → Value V
    → M —→ M'
      ---------------------------------------
    → `* V M —→ `* V M'


  -- Left compatibility rule for =
  ξ-=₁ : ∀ {Γ : Context} {L L' M : Γ ⊢ `Num}
    → L —→ L'
      -------------------------------------
    → `= L M —→ `= L' M


  -- Right compatibility rule for =
  ξ-=₂ : ∀ {Γ : Context} {V M M' : Γ ⊢ `Num}
    → Value V
    → M —→ M'
      ---------------------------------------
    → `= V M —→ `= V M'


  -- Left compatibility rule for <
  ξ-<₁ : ∀ {Γ : Context} {L L' M : Γ ⊢ `Num}
    → L —→ L'
      -------------------------------------
    → `< L M —→ `< L' M


  -- Right compatibility rule for <
  ξ-<₂ : ∀ {Γ : Context} {V M M' : Γ ⊢ `Num}
    → Value V
    → M —→ M'
      ---------------------------------------
    → `< V M —→ `< V M'


  -- Left compatibility rule for ∧
  ξ-∧₁ : ∀ {Γ : Context} {L L' M : Γ ⊢ `𝔹}
    → L —→ L'
      -------------------------------------
    → `∧ L M —→ `∧ L' M


  -- Right compatibility rule for <
  ξ-∧₂ : ∀ {Γ : Context} {V M M' : Γ ⊢ `𝔹}
    → Value V
    → M —→ M'
      ---------------------------------------
    → `∧ V M —→ `∧ V M'


  -- Left compatibility rule for ∨
  ξ-∨₁ : ∀ {Γ : Context} {L L' M : Γ ⊢ `𝔹}
    → L —→ L'
      -------------------------------------
    → `∨ L M —→ `∨ L' M


  -- Right compatibility rule for ∨
  ξ-∨₂ : ∀ {Γ : Context} {V M M' : Γ ⊢ `𝔹}
    → Value V
    → M —→ M'
      ---------------------------------------
    → `∨ V M —→ `∨ V M'


  -- Reduction rule for primitive `+
  β-+ : ∀ {Γ : Context} {m n : ℕ}
      ----------------------------
    → `+ (eNum {Γ} n) (eNum {Γ} m) —→ eNum {Γ} (n + m)


  -- Reduction rule for primitive `*
  β-* : ∀ {Γ : Context} {m n : ℕ}
      ----------------------------
    → `* (eNum {Γ} n) (eNum {Γ} m) —→ eNum {Γ} (n * m)


  -- Reduction rule for primitive `=
  β-= : ∀ {Γ : Context} {m n : ℕ}
      ----------------------------
    → `= (eNum {Γ} n) (eNum {Γ} m) —→ eBool {Γ} (n == m)


  -- Reduction rule for primitive `<
  β-< : ∀ {Γ : Context} {m n : ℕ}
      ----------------------------
    → `< (eNum {Γ} n) (eNum {Γ} m) —→ eBool {Γ} (n < m)


  -- Reduction rule for primitive `∧
  β-∧ : ∀ {Γ : Context} {x y : Bool}
      ----------------------------
    → `∧ (eBool {Γ} x) (eBool {Γ} y) —→ eBool {Γ} (and x y)


  -- Reduction rule for primitive `∨
  β-∨ : ∀ {Γ : Context} {x y : Bool}
      ----------------------------
    → `∨ (eBool {Γ} x) (eBool {Γ} y) —→ eBool {Γ} (or x y)


  -- condition compatibility rule for eIf
  ξ-if₀ : ∀ {Γ : Context} {A : Type} {L L' : Γ ⊢ `𝔹} {M N : Γ ⊢ A}
    → L —→ L'
      ------------------------------------------------------------
    → eIf L M N —→ eIf L' M N


  -- eIf reduction on true
  β-if₁ : ∀ {Γ : Context} {A : Type} {M N : Γ ⊢ A}
      ------------------------------------------------------------
    → eIf (eBool {Γ} true) M N —→ M


  -- eIf reduction on false
  β-if₂ : ∀ {Γ : Context} {A : Type} {M N : Γ ⊢ A}
      ------------------------------------------------------------
    → eIf (eBool {Γ} false) M N —→ N


  -- Left compatibility rule for ·
  ξ-·₁ : ∀ {Γ : Context} {A B : Type} {L L' : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L'
      --------------------------------------------------------------
    → L · M —→ L' · M


  -- Right compatibility rule for ·
  ξ-·₂ : ∀ {Γ : Context} {A B : Type} {V : Γ ⊢ A ⇒ B} {M M' : Γ ⊢ A}
    → Value V
    → M —→ M'
      ---------------------------------------------------------------
    → V · M —→ V · M'


  -- Beta reduction rule for abstraction
  β-ƛ : ∀ {Γ : Context} {A B : Type} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      ----------------------------------------------------------
    → (ƛ N) · W —→ N [ W ]


  -- Compatibility rule for suc
  ξ-suc : ∀ {Γ : Context} {M M' : Γ ⊢ `ℕ}
    → M —→ M'
      -----------------------------------
    → `suc M —→ `suc M'


  -- Compatibility rule for case
  ξ-case : ∀ {Γ : Context} {A : Type} {L L' : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → L —→ L'
      -----------------------------------------------------------------------------
    → case L M N —→ case L' M N


  -- Beta reduction rule for case (zero)
  β-zero : ∀ {Γ : Context} {A : Type} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
      ------------------------------------------------------------
    → case `zero M N —→ M


  -- Beta reduction rule for case (suc)
  β-suc : ∀ {Γ : Context} {A : Type} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → Value V
      ------------------------------------------------------------
    → case (`suc V) M N —→ N [ V ]


  -- Beta reduction rule for fixed point
  β-μ : ∀  {Γ : Context} {A : Type} {N : Γ , A ⊢ A}
      ---------------------------------------------
    →  μ N —→ N [ μ N ]


valueReduce : ∀ {Γ : Context} {A : Type} {M N : Γ ⊢ A} →
  Value M → M —→ N → ⊥
valueReduce (V-suc p) (ξ-suc q) = valueReduce p q

det : ∀ {Γ : Context} {A : Type} {M N N' : Γ ⊢ A}
  → M —→ N
  → M —→ N'
    -------
  → N ≡ N'

det (ξ-+₁ p) (ξ-+₁ q) = cong _ (det p q)
det (ξ-+₁ p) (ξ-+₂ q r) = ⊥-elim (valueReduce q p)
det (ξ-+₂ p q) (ξ-+₁ r) = ⊥-elim (valueReduce p r)
det (ξ-+₂ p q) (ξ-+₂ r s) = cong _ (det q s)
det (ξ-*₁ p) (ξ-*₁ q) = cong _ (det p q)
det (ξ-*₁ p) (ξ-*₂ q r) = ⊥-elim (valueReduce q p )
det (ξ-*₂ p q) (ξ-*₁ r) = ⊥-elim (valueReduce p r)
det (ξ-*₂ p q) (ξ-*₂ r s) = cong _ (det q s)
det (ξ-=₁ p) (ξ-=₁ q) = cong _ (det p q)
det (ξ-=₁ p) (ξ-=₂ q r) = ⊥-elim (valueReduce q p)
det (ξ-=₂ p q) (ξ-=₁ r) = ⊥-elim (valueReduce p r)
det (ξ-=₂ p q) (ξ-=₂ r s) = cong _ (det q s)
det (ξ-<₁ p) (ξ-<₁ q) = cong _ (det p q)
det (ξ-<₁ p) (ξ-<₂ q r) = ⊥-elim (valueReduce q p)
det (ξ-<₂ p q) (ξ-<₁ r) = ⊥-elim (valueReduce p r)
det (ξ-<₂ p q) (ξ-<₂ r s) = cong _ (det q s)
det (ξ-∧₁ p) (ξ-∧₁ q) = cong _ (det p q)
det (ξ-∧₁ p) (ξ-∧₂ q r) = ⊥-elim (valueReduce q p)
det (ξ-∧₂ p q) (ξ-∧₁ r) = ⊥-elim (valueReduce p r)
det (ξ-∧₂ p q) (ξ-∧₂ r s) = cong _ (det q s)
det (ξ-∨₁ p) (ξ-∨₁ q) = cong _ (det p q)
det (ξ-∨₁ p) (ξ-∨₂ q r) = ⊥-elim (valueReduce q p )
det (ξ-∨₂ x p) q = {!!}
det β-+ q = {!!}
det β-* q = {!!}
det β-= q = {!!}
det β-< q = {!!}
det β-∧ q = {!!}
det β-∨ q = {!!}
det (ξ-if₀ p) q = {!!}
det β-if₁ q = {!!}
det β-if₂ q = {!!}
det (ξ-·₁ p) q = {!!}
det (ξ-·₂ x p) q = {!!}
det (β-ƛ x) q = {!!}
det (ξ-suc p) q = {!!}
det (ξ-case p) q = {!!}
det β-zero q = {!!}
det (β-suc x) q = {!!}
det β-μ q = {!!}




