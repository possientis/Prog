import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.List using (List; _∷_; []; concat; map; zip)
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

f₁ : ∀ {a : Set} → (p : a → Bool) → List a → List a × List Bool
f₁ p = pair (id , map p)

f₂ : ∀ {a : Set} → (p : a → Bool) → List a -> List (a × Bool)
f₂ p = {!!}


L1 : ∀ {a : Set} → {p : a → Bool} →
  map proj₁ ∘ filter proj₂ ∘ uncurry zip ∘ (pair (id , map p)) ≡ filter p

L1 {a} {p} =
  begin
    map proj₁ ∘ filter proj₂ ∘ uncurry zip ∘ (pair (id , map p))
    ≡⟨⟩
    {!!}


