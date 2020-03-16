import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.List using (List; _∷_; []; concat; map; zip; _++_)
open import Data.Product using (_×_; proj₁; proj₂; _,_; uncurry)
open import Data.Bool using (Bool; true; false)
open import Function using (_∘_; id)

postulate
  extensionality : ∀ {a b : Set} {f g : a → b}
    → (∀ (x : a) → f x ≡ g x)
      -----------------------
    →         f ≡ g

_~>_,_ : ∀ {a b : Set} → (a → Bool) → (a → b) → (a → b) → a → b
(p ~> f , g) x with p x
(p ~> f , g) x | false = g x
(p ~> f , g) x | true = f x

nilp : ∀ {a : Set} → a → List a
nilp x = []

wrap : ∀ {a : Set} → a → List a
wrap x = x ∷ []

filter : ∀ {a : Set} → (a → Bool) → List a → List a
filter {a} p = concat ∘ map (p ~> wrap , nilp)

pair : ∀ {a b c : Set} → (a → b) × (a → c) → a → b × c
pair (f , g) x = (f x , g x)



concatNat : ∀ {a b : Set} → (f : a → b) → (xss : List (List a)) →
  (map f ∘ concat) xss ≡ (concat ∘ map (map f)) xss
concatNat f [] = refl
concatNat f ([] ∷ xss) =
  begin
    (map f ∘ concat) ([] ∷ xss)
    ≡⟨⟩
    map f (concat ([] ∷ xss))
    ≡⟨⟩
    map f ([] ++ concat xss)
    ≡⟨⟩
    map f (concat xss)
    ≡⟨⟩
    (map f ∘ concat) xss
    ≡⟨ concatNat f xss ⟩
    (concat ∘ map (map f)) xss
    ≡⟨⟩
    concat (map (map f) xss)
    ≡⟨⟩
    [] ++ concat (map (map f) xss)
    ≡⟨⟩
    concat ([] ∷ map (map f) xss)
    ≡⟨⟩
    concat (map (map f) ([] ∷ xss))
    ≡⟨⟩
    (concat ∘ (map (map f))) ([] ∷ xss)
    ∎

concatNat f ((x ∷ xs) ∷ xss) =
  begin
    (map f ∘ concat) ((x ∷ xs) ∷ xss)
    ≡⟨⟩
    map f (concat ((x ∷ xs) ∷ xss))
    ≡⟨⟩
    map f ((x ∷ xs) ++ concat xss)
    ≡⟨⟩
    map f (x ∷ (xs ++ concat xss))
    ≡⟨⟩
    f x ∷ map f (xs ++ concat xss)
    ≡⟨⟩
    f x ∷ map f (concat (xs ∷ xss))
    ≡⟨⟩
    f x ∷ ((map f ∘ concat) (xs ∷ xss))
    ≡⟨⟩ {!!}



L1 : ∀ {a : Set} → {p : a → Bool} →
  map proj₁ ∘ filter proj₂ ∘ uncurry zip ∘ (pair (id , map p)) ≡ filter p

L1 {a} {p} =
  begin
    map proj₁ ∘ filter proj₂ ∘ uncurry zip ∘ (pair (id , map p))
    ≡⟨⟩
    map proj₁ ∘ concat ∘ map (proj₂ ~> wrap , nilp) ∘ uncurry zip ∘ (pair (id , map p))
    ≡⟨⟩ {!!}


