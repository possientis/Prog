module DeBruijn.Context where

open import Data.Nat                     using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)

open import Lam.Type

infixl 5 _,_
infix 4 _∋_
infix 9 S_
infix 4 _⊆_

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

length : Context → ℕ
length ∅ = zero
length (Γ , _) = suc (length Γ)

lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
lookup {_ , A} {zero} (s≤s z≤n) = A
lookup {_ , _} {suc n} (s≤s p) = lookup p

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ : Context} {A : Type}
      ------------------------------
    → Γ , A ∋ A

  S_ : ∀ {Γ : Context} {A B : Type}
    →  Γ ∋ A
       ------------------------------
    →  Γ , B ∋ A

count : ∀ {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
count {_ , _} {zero} (s≤s z≤n) = Z
count {Γ , A} {suc n} (s≤s p) = S (count p)

_⊆_ : Context -> Context -> Set
_⊆_ Γ Δ = ∀ {A : Type } → Γ ∋ A → Δ ∋ A


⊆-refl : ∀ {Γ : Context} → Γ ⊆ Γ
⊆-refl p = p

⊆-trans : ∀ {Γ Δ Ε : Context} → Γ ⊆ Δ → Δ ⊆ Ε → Γ ⊆ Ε
⊆-trans p q r = q (p r)

ext : ∀ {Γ Δ : Context} {A : Type}
  →   Γ ⊆ Δ
      --------------
  →   Γ , A ⊆ Δ , A

ext f Z = Z
ext f (S p) = S f p



