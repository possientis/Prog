module Lam.Context where

open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; subst;cong)

open import Data.Nat                     using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.String                  using (String; _≟_) -- \?=
open import Data.Product                 using (_×_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Product                 using () renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Decidable   using (False;toWitnessFalse)

open import Lam.Id
open import Lam.Type

infixl 5 _,_∶_  -- \:
infix 4 _∋_∶_ -- \ni

data Context : Set where
  ∅     : Context -- \0
  _,_∶_ : Context → Id → Type → Context

length : Context → ℕ
length ∅ = zero
length (Γ , _ ∶ _) = suc (length Γ)

lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Id × Type
lookup {_ , x ∶ A} {zero} (s≤s z≤n) = ⟨ x , A ⟩
lookup {_ , _ ∶ _} {suc n} (s≤s p) = lookup p

data _∋_∶_ : Context → Id → Type → Set where

  Z : ∀ {Γ : Context}{x : Id}{A : Type}
      ---------------------------------
    → Γ , x ∶ A ∋ x ∶  A

  S : ∀ {Γ : Context}{x y : Id}{A B : Type}
    → x ≢ y -- \==n
    → Γ ∋ x ∶ A
      ---------------------------------
    → Γ , y ∶ B ∋ x ∶ A
 

-- smart constructor using proof by reflection

S' : ∀ {Γ : Context} {x y : Id} {A B : Type}
  → {x≢y : False (x ≟ y) }
  → Γ ∋ x ∶ A
    ----------------------------------
  → Γ , y ∶ B ∋ x ∶ A
S' {x≢y = x≢y} x = S (toWitnessFalse x≢y) x


_⊆_ : Context → Context → Set
Γ ⊆ Δ = ∀ {x : Id} {A : Type} → Γ ∋ x ∶ A → Δ ∋ x ∶ A

infix 4 _⊆_

ext : ∀ {Γ Δ : Context} {y : Id} {B : Type}
  →   Γ ⊆ Δ
     ---------------
  →   Γ , y ∶ B ⊆ Δ , y ∶ B

ext f Z = Z
ext f (S p q) = S p (f q)
