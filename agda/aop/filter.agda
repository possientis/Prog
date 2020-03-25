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

∘-distrib-~>-l : ∀ {a b c : Set} → (p : a → Bool) → (f g : a → b) → (h : b → c) →
  h ∘ (p ~> f , g) ≡ (p ~> (h ∘ f) , (h ∘ g))
∘-distrib-~>-l {a} {b} {c} p f g h = extensionality k
  where
    k : ∀ (x : a) → (h ∘ (p ~> f , g)) x ≡ (p ~> (h ∘ f) , (h ∘ g)) x
    k x with p x
    k x | false = refl
    k x | true = refl

nilp : ∀ {a : Set} → a → List a
nilp x = []

nilpNat : ∀ {a b : Set} → (f : a → b) → map f ∘ nilp ≡ nilp ∘ f
nilpNat {a} {b} f = extensionality k
  where
    k : ∀ (x : a) → (map f ∘ nilp) x ≡ (nilp ∘ f) x
    k x = refl

wrap : ∀ {a : Set} → a → List a
wrap x = x ∷ []

filter : ∀ {a : Set} → (a → Bool) → List a → List a
filter {a} p = concat ∘ map (p ~> wrap , nilp)

pair : ∀ {a b c : Set} → (a → b) × (a → c) → a → b × c
pair (f , g) x = (f x , g x)

-- Lemma needed to prove concatNat
concatNat' : ∀ {a b : Set} → (f : a → b) → (xss : List (List a)) →
  (map f ∘ concat) xss ≡ (concat ∘ map (map f)) xss
concatNat' f [] = refl
concatNat' f ([] ∷ xss) =
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
    ≡⟨ concatNat' f xss ⟩
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

concatNat' f ((x ∷ xs) ∷ xss) =
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
    ≡⟨ cong (f x ∷_) (concatNat' f ((xs ∷ xss))) ⟩
    f x ∷ ((concat ∘ (map (map f))) (xs ∷ xss))
    ≡⟨⟩
    f x ∷ (concat (map (map f) (xs ∷ xss)))
    ≡⟨⟩
    f x ∷ (concat ((map f xs) ∷ (map (map f) xss)))
    ≡⟨⟩
    f x ∷ ((map f xs) ++ concat (map (map f) xss))
    ≡⟨⟩
    (f x ∷ map f xs) ++ concat (map (map f) xss)
    ≡⟨⟩
    map f (x ∷ xs) ++ concat (map (map f) xss)
    ≡⟨⟩
    concat (map f (x ∷ xs) ∷ map (map f) xss)
    ≡⟨⟩
    concat (map (map f) ((x ∷ xs) ∷ xss))
    ≡⟨⟩
    (concat ∘ (map (map f))) ((x ∷ xs) ∷ xss)
    ∎

-- 'concat : List (List a) → List a' is a natural transformation 'concat : List² ⇒ List'
concatNat : ∀ {a b : Set} → (f : a → b) → map f ∘ concat ≡ concat ∘ map (map f)
concatNat f = extensionality (concatNat' f)

∘-map' : ∀ {a b c : Set} → {f : a → b} → {g : b → c} → (xs : List a) →
  map (g ∘ f) xs ≡ (map g ∘ map f) xs

∘-map' [] = refl
∘-map' {f = f} {g} (x ∷ xs) =
  begin
    map (g ∘ f) (x ∷ xs)
    ≡⟨⟩
    (g ∘ f) x ∷ map (g ∘ f) xs
    ≡⟨ cong ((g ∘ f) x ∷_) (∘-map' xs) ⟩
    (g ∘ f) x ∷ (map g ∘ map f) xs
    ≡⟨⟩
    g (f x) ∷ (map g (map f xs))
    ≡⟨⟩
    map g (f x ∷ map f xs)
    ≡⟨⟩
    map g (map f (x ∷ xs))
    ≡⟨⟩
    (map g ∘ map f) (x ∷ xs)
    ∎

∘-map : ∀ {a b c : Set} → {f : a → b} → {g : b → c} → map (g ∘ f) ≡ map g ∘ map f
∘-map = extensionality ∘-map'


L1 : ∀ {a : Set} → {p : a → Bool} →
  map proj₁ ∘ filter proj₂ ∘ uncurry zip ∘ pair (id , map p) ≡ filter p

L1 {a} {p} =
  begin
    map proj₁ ∘ filter proj₂ ∘ uncurry zip ∘ pair (id , map p)
    ≡⟨⟩         -- definition of filter
    map proj₁ ∘ concat ∘ map (proj₂ ~> wrap , nilp) ∘ uncurry zip ∘ pair (id , map p)
    ≡⟨ cong     -- concat is natural
         (λ { f → f ∘ map (proj₂ ~> wrap , nilp) ∘ uncurry zip ∘ pair (id , map p)})
         (concatNat proj₁)⟩
    concat ∘ map (map proj₁) ∘ map (proj₂ ~> wrap , nilp) ∘ uncurry zip ∘ pair (id , map p)
    ≡⟨ cong (λ { h → concat ∘ h ∘ uncurry zip ∘ pair (id , map p) }) (sym ∘-map) ⟩
    concat ∘ map (map proj₁ ∘ (proj₂ ~> wrap , nilp)) ∘ uncurry zip ∘ pair (id , map p)
    ≡⟨ cong (λ { f → concat ∘ map f ∘ uncurry zip ∘ pair (id , map p) }) (∘-distrib-~>-l proj₂ wrap nilp (map proj₁)) ⟩
    concat ∘ map (proj₂ ~> (map proj₁ ∘ wrap) , (map proj₁ ∘ nilp)) ∘ uncurry zip ∘ pair (id , map p)
    ≡⟨ cong (λ { f → concat ∘ map (proj₂ ~> (map proj₁ ∘ wrap) , f) ∘ uncurry zip ∘ pair (id , map p)}) (nilpNat proj₁) ⟩
    concat ∘ map (proj₂ ~> (map proj₁ ∘ wrap) , (nilp ∘ proj₁)) ∘ uncurry zip ∘ pair (id , map p)
    ≡⟨⟩ {!!}


