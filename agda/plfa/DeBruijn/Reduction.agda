module DeBruijn.Reduction where

open import Data.Nat            using (ℕ; zero; suc; _+_; _*_)
open import Data.Bool           using (Bool;true;false)

open import Lam.Type
open import Lam.Prim
open import DeBruijn.Value
open import DeBruijn.Syntax
open import DeBruijn.Context

infix 2 _—→_ -- \em\to

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

  ξ-if₀ : ∀ {Γ : Context} {A : Type} {L L' : Γ ⊢ `𝔹} {M N : Γ ⊢ A}
    → L —→ L'
      ------------------------------------------------------------
    → eIf L M N —→ eIf L' M N

