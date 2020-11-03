module Lam.Cong where

open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; sym; cong)

cong₄ : ∀ {a b c d e : Set} (f : a → b → c → d → e)
  {x₁ x₂ : a} {y₁ y₂ : b} {z₁ z₂ : c} {t₁ t₂ : d} →
  x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → t₁ ≡ t₂ →
  f x₁ y₁ z₁ t₁ ≡ f x₂ y₂ z₂ t₂
cong₄ f refl refl refl refl = refl
