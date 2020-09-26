module Lam.Typing where

open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; subst;cong)

open import Data.Empty       using (⊥; ⊥-elim)

open import Data.Nat
open import Data.Bool

open import Lam.Id
open import Lam.Op
open import Lam.Type
open import Lam.Syntax
open import Lam.Context

infix 4 _⊢_∶_ -- \vdash for ⊢ and \: for ∶

data _⊢_∶_ : Context → Term → Type → Set where

  -- Axiom
  ⊢` : ∀ {Γ : Context} {x : Id} {A : Type}
    → Γ ∋ x ∶ A
      --------------------
    → Γ ⊢ ` x ∶ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ : Context} {x : Id} {N : Term} {A B : Type}
    → Γ , x ∶ A ⊢ N ∶ B
      --------------------
    → Γ ⊢ ƛ x ⇒ N ∶ A ⇒ B

  -- ⇒-E
  ⊢· : ∀ {Γ : Context} {L M : Term} {A B : Type}
    → Γ ⊢ L ∶ A ⇒ B
    → Γ ⊢ M ∶ A
      --------------------
    → Γ ⊢ L · M ∶ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ : Context}
      --------------------
    → Γ ⊢ `zero ∶ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ : Context} {M : Term}
    → Γ ⊢ M ∶ `ℕ
      --------------------
    → Γ ⊢ `suc M ∶ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ : Context} {L M N : Term} {x : Id} {A : Type}
    → Γ ⊢ L ∶ `ℕ
    → Γ ⊢ M ∶ A
    → Γ , x ∶ `ℕ ⊢ N ∶ A
      --------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ∶ A

  -- 𝔹-E
  ⊢if : ∀ {Γ : Context} {L M N : Term} {A : Type}
    → Γ ⊢ L ∶ `𝔹
    → Γ ⊢ M ∶ A
    → Γ ⊢ N ∶ A
     ---------------
    → Γ ⊢ eIf L M N ∶ A

  -- μ-I
  ⊢μ : ∀ {Γ : Context} {x : Id} {M : Term} {A : Type}
    → Γ , x ∶ A ⊢ M ∶ A
      --------------------
    → Γ ⊢ μ x ⇒ M ∶ A

  -- Num-I₁
  ⊢Num : ∀ {Γ : Context} {n : ℕ}
       ---------------------
    →  Γ ⊢ (eNum n) ∶ `Num

  -- Num-I₂
  ⊢+ : ∀ {Γ : Context} {M N : Term}
    → Γ ⊢ M ∶ `Num
    → Γ ⊢ N ∶ `Num
      ---------------
    → Γ ⊢ eOp `+ M N ∶ `Num

  -- Num-I₃
  ⊢* : ∀ {Γ : Context} {M N : Term}
    → Γ ⊢ M ∶ `Num
    → Γ ⊢ N ∶ `Num
      ---------------
    → Γ ⊢ eOp `* M N ∶ `Num

  -- Bool-I₁
  ⊢Bool : ∀ {Γ : Context} {b : Bool}
        --------------------
    →  Γ ⊢ (eBool b) ∶ `𝔹

  -- Bool-I₂
  ⊢= : ∀ {Γ : Context} {M N : Term}
    → Γ ⊢ M ∶ `Num
    → Γ ⊢ N ∶ `Num
      ---------------
    → Γ ⊢ eOp `= M N ∶ `𝔹

  -- Bool-I₃
  ⊢< : ∀ {Γ : Context} {M N : Term}
    → Γ ⊢ M ∶ `Num
    → Γ ⊢ N ∶ `Num
      ---------------
    → Γ ⊢ eOp `< M N ∶ `𝔹

  -- Bool-I₄
  ⊢∧ : ∀ {Γ : Context} {M N : Term}
    → Γ ⊢ M ∶ `𝔹
    → Γ ⊢ N ∶ `𝔹
      ---------------
    → Γ ⊢ eOp `∧ M N ∶ `𝔹

  -- Bool-I₅
  ⊢∨ : ∀ {Γ : Context} {M N : Term}
    → Γ ⊢ M ∶ `𝔹
    → Γ ⊢ N ∶ `𝔹
      ---------------
    → Γ ⊢ eOp `∨ M N ∶ `𝔹


rename : ∀ {Γ Δ : Context} {M : Term} {A : Type} → Γ ⊆ Δ → Γ ⊢ M ∶ A → Δ ⊢ M ∶ A
rename f (⊢` p) = ⊢` (f p)
rename f (⊢ƛ p) = ⊢ƛ (rename (ext f) p)
rename f (⊢· p q) = ⊢· (rename f p) (rename f q)
rename f ⊢zero = ⊢zero
rename f (⊢suc p) = ⊢suc (rename f p)
rename f (⊢case p q r) = ⊢case (rename f p) (rename f q) (rename (ext f) r)
rename f (⊢if p q r) = ⊢if (rename f p) (rename f q) (rename f r)
rename f (⊢μ p) = ⊢μ (rename (ext f) p)
rename f ⊢Num = ⊢Num
rename f (⊢+ p q) = ⊢+ (rename f p) (rename f q)
rename f (⊢* p q) = ⊢* (rename f p) (rename f q)
rename f ⊢Bool = ⊢Bool
rename f (⊢= p q) = ⊢= (rename f p) (rename f q)
rename f (⊢< p q) = ⊢< (rename f p) (rename f q)
rename f (⊢∧ p q) = ⊢∧ (rename f p) (rename f q)
rename f (⊢∨ p q) = ⊢∨ (rename f p) (rename f q)

weaken : ∀ {Γ : Context} {M : Term} {A : Type}
  → ∅ ⊢ M ∶ A
    ---------------
  → Γ ⊢ M ∶ A

weaken {Γ} p = rename ρ p
  where
    ρ : ∀ {x : Id} {A : Type} → ∅ ∋ x ∶ A → Γ ∋ x ∶ A
    ρ ()

drop : ∀ {Γ : Context} {x : Id} {M : Term} {A B C : Type}
  → Γ , x ∶ A , x ∶ B ⊢ M ∶ C
    ------------------------------
  → Γ , x ∶ B ⊢ M ∶ C

drop {Γ} {x} {M} {A} {B} p = rename {!!} p
  where
    ρ : ∀ {y : Id} {D : Type} → Γ , x ∶ A , x ∶ B ∋ y ∶ D → Γ , x ∶ B ∋ y ∶ D
    ρ Z = Z
    ρ {x} {D} (S p Z) = S p (⊥-elim (p refl))
    ρ {x} {D} (S p (S q r)) = S p r

swap : ∀ {Γ : Context} {x y : Id} {M : Term} {A B C : Type}
  → x ≢ y        -- \==n
  → Γ , y ∶ B , x ∶ A ⊢ M ∶ C
    -------------------------
  → Γ , x ∶ A , y ∶ B ⊢ M ∶ C

swap {Γ} {x} {y} {M} {A} {B} {C} x≢y p = rename ρ p
  where
    ρ : ∀ {z : Id} {D : Type} → Γ , y ∶ B , x ∶ A ∋ z ∶ D → Γ , x ∶ A , y ∶ B ∋ z ∶ D
    ρ {z} {D} Z = S x≢y Z
    ρ {z} {D} (S p Z) = Z
    ρ {z} {D} (S p (S q r)) = S q (S p r)
