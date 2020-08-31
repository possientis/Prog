open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; sym; cong)

open import Data.String      using (String; _≟_) -- \?=
open import Data.Nat         using (ℕ; zero; suc)
open import Data.Empty       using (⊥; ⊥-elim)
open import Data.Product     using (_×_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Product     using () renaming (_,_ to ⟨_,_⟩)
open import Data.Sum         using (_⊎_; inj₁; inj₂)
open import Data.Bool        using (Bool; true; false)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Function         using (_∘_)

open import isomorphism

open import Lam.Id
open import Lam.Op
open import Lam.Type
open import Lam.Value
open import Lam.Typing
open import Lam.Syntax
open import Lam.Context
open import Lam.Reduction

V¬—→ : ∀ {M N : Term}
  → Value M
    ---------------
  → ¬ (M —→ N)

V¬—→ (V-suc p) (ξ-suc q) = V¬—→ p q


—→¬V : ∀ {M N : Term}
  →  M —→ N
    ----------
  →  ¬ Value M

—→¬V p q = V¬—→ q p

infix 4 Canonical_∶_

data Canonical_∶_ : Term → Type → Set where

  C-ƛ : ∀ {x : Id} {A B : Type} {N : Term}
    →  ∅ , x ∶ A ⊢ N ∶ B
      --------------------
    → Canonical (ƛ x ⇒ N) ∶ A ⇒ B

  C-zero :
      ---------------------
      Canonical `zero ∶ `ℕ

  C-suc : ∀ {V : Term}
    →  Canonical V ∶ `ℕ
      --------------------
    → Canonical (`suc V) ∶ `ℕ

  C-Num : ∀ {n : ℕ}
      ---------------------
    → Canonical (eNum n) ∶ `Num

  C-Bool : ∀ {b : Bool}
      ----------------------
    → Canonical (eBool b) ∶ `𝔹

  C-+ : ∀ {M N : Term}
    →  Canonical M ∶ `Num
    →  Canonical N ∶ `Num
      -----------------------
    →  Canonical (eOp `+ M N) ∶ `Num

  C-* : ∀ {M N : Term}
    → Canonical M ∶ `Num
    → Canonical N ∶ `Num
      --------------------
    → Canonical (eOp `* M N) ∶ `Num
