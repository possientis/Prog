module lists where


import Relation.Binary.PropositionalEquality as Eq

open Eq                         using ( _≡_; refl; trans; sym; cong)
open Eq.≡-Reasoning             using ( begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Bool           using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat            using ( ℕ; zero; suc; _≤_; z≤n; s≤s; _+_; _*_)
open import Relation.Nullary    using ( Dec; yes; no; ¬_)
open import Data.Nat.Properties using (+-assoc; +-suc; +-comm)
open import Data.Product        using ( _×_; ∃; ∃-syntax)
open import Function            using (_∘_)
open import Level               using (Level)
open import isomorphism         using (_≃_; _⇔_)


data List (a : Set) : Set where
  []  : List a
  _∷_ : a → List a → List a

infixr 5 _∷_

_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ 3 ∷ []

data List' : Set → Set where
  []'  : ∀ {a : Set} → List' a
  _∷'_ : ∀ {a : Set} → a → List' a → List' a

_ : List ℕ
_ = _∷_ {ℕ} 0 (_∷_ {ℕ} 1 (_∷_ {ℕ} 2 ([] {ℕ})))

{-# BUILTIN LIST List #-}


pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_

_++_ : ∀ {a : Set} → List a → List a → List a
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys -- both ∷ and ++ are right-assoc with bind level 5

_ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
_ =
  begin
    [ 0 , 1 , 2 ] ++ [ 3 , 4 ]
    ≡⟨⟩
     0 ∷ [ 1 , 2 ] ++ [ 3 , 4 ]
    ≡⟨⟩
    0 ∷ 1 ∷ [ 2 ] ++ [ 3 , 4 ]
    ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ [] ++ [ 3 , 4 ]
    ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ [ 3 , 4 ]
    ≡⟨⟩
    [ 0 , 1 , 2 , 3 , 4 ]
    ∎


++-assoc : ∀ {a : Set} → (xs ys zs : List a) →
  (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs =
  begin
     ((x ∷ xs) ++ ys) ++ zs
     ≡⟨⟩
     (x ∷ (xs ++ ys)) ++ zs
     ≡⟨⟩
     x ∷ ((xs ++ ys) ++ zs)
     ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
     x ∷ (xs ++ (ys ++ zs))
     ≡⟨⟩
     (x ∷ xs) ++ (ys ++ zs)
     ∎

