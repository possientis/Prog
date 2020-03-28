import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.List    using (List; _∷_; []; concat; map; _++_; zip)
open import Data.Product using (_×_; proj₁; proj₂; _,_; uncurry)
open import Data.Bool    using (Bool; true; false)
open import Function     using (_∘_; id)


postulate
  extensionality : ∀ {a b : Set} {f g : a → b}
    → (∀ (x : a) → f x ≡ g x)
      -----------------------
    →         f ≡ g


_~>_,_ : ∀ {a b : Set} → (a → Bool) → (a → b) → (a → b) → a → b
(p ~> f , g) x with p x
(p ~> f , g) x | false = g x
(p ~> f , g) x | true  = f x

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

-- nilp is a natural transformation nilp : Id ⇒ List
nilpNat : ∀ {a b : Set} → (f : a → b) → map f ∘ nilp ≡ nilp ∘ f
nilpNat {a} {b} f = extensionality k
  where
    k : ∀ (x : a) → (map f ∘ nilp) x ≡ (nilp ∘ f) x
    k x = refl


wrap : ∀ {a : Set} → a → List a
wrap x = x ∷ []

-- wrap is a natural transformation wrap : Id ⇒ List
wrapNat : ∀ {a b : Set} → (f : a → b) -> map f ∘ wrap ≡ wrap ∘ f
wrapNat {a} {b} f = extensionality k
  where
    k : ∀ (x : a) → (map f ∘ wrap) x ≡ (wrap ∘ f) x
    k x = refl


-- point-free definition of filter
filter : ∀ {a : Set} → (a → Bool) → List a → List a
filter {a} p = concat ∘ map (p ~> wrap , nilp)


⟨_,_⟩ : ∀ {a b c : Set} → (a → b) → (a → c) → a → b × c
⟨ f , g ⟩ x = (f x , g x)


-- concat : List (List a) → List a is a natural transformation concat : List² ⇒ List
concatNat : ∀ {a b : Set} → {f : a → b} → map f ∘ concat ≡ concat ∘ map (map f)
concatNat {a} {b} = extensionality k
  where
    k : ∀ {a b : Set} → {f : a → b} → (xss : List (List a)) →
      (map f ∘ concat) xss ≡ (concat ∘ map (map f)) xss
    k [] = refl
    k {f = f}([] ∷ xss) =
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
        ≡⟨ k xss ⟩
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
    k {f = f} ((x ∷ xs) ∷ xss) =
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
        ≡⟨ cong (f x ∷_) (k ((xs ∷ xss))) ⟩
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

∘-map : ∀ {a b c : Set} → {f : a → b} → {g : b → c} → map (g ∘ f) ≡ map g ∘ map f
∘-map = extensionality k
  where
    k : ∀ {a b c : Set} → {f : a → b} → {g : b → c} → (xs : List a) →
      map (g ∘ f) xs ≡ (map g ∘ map f) xs
    k [] = refl
    k {f = f} {g} (x ∷ xs) =
      begin
        map (g ∘ f) (x ∷ xs)
        ≡⟨⟩
        (g ∘ f) x ∷ map (g ∘ f) xs
        ≡⟨ cong ((g ∘ f) x ∷_) (k xs) ⟩
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


L1 : ∀ {a : Set} → {p : a → Bool} →
  map proj₁ ∘ filter proj₂ ∘ uncurry zip ∘ ⟨ id , map p ⟩ ≡ filter p

L1 {a} {p} =
  begin
    map proj₁ ∘ filter proj₂ ∘ uncurry zip ∘ ⟨ id , map p ⟩
    ≡⟨⟩         -- definition of filter
    map proj₁ ∘ concat ∘ map (proj₂ ~> wrap , nilp) ∘ uncurry zip ∘ ⟨ id , map p ⟩
    ≡⟨ cong     -- concat is natural
         (λ { f → f ∘ map (proj₂ ~> wrap , nilp) ∘ uncurry zip ∘ ⟨ id , map p ⟩})
         concatNat ⟩
    concat ∘ map (map proj₁) ∘ map (proj₂ ~> wrap , nilp) ∘ uncurry zip ∘ ⟨ id , map p ⟩
    ≡⟨ cong (λ { h → concat ∘ h ∘ uncurry zip ∘ ⟨ id , map p ⟩ }) (sym ∘-map) ⟩
    concat ∘ map (map proj₁ ∘ (proj₂ ~> wrap , nilp)) ∘ uncurry zip ∘ ⟨ id , map p ⟩
    ≡⟨ cong (λ { f → concat ∘ map f ∘ uncurry zip ∘ ⟨ id , map p ⟩ }) (∘-distrib-~>-l proj₂ wrap nilp (map proj₁)) ⟩
    concat ∘ map (proj₂ ~> (map proj₁ ∘ wrap) , (map proj₁ ∘ nilp)) ∘ uncurry zip ∘ ⟨ id , map p ⟩
    ≡⟨ cong (λ { f → concat ∘ map (proj₂ ~> (map proj₁ ∘ wrap) , f) ∘ uncurry zip ∘ ⟨ id , map p ⟩}) (nilpNat proj₁) ⟩
    concat ∘ map (proj₂ ~> (map proj₁ ∘ wrap) , (nilp ∘ proj₁)) ∘ uncurry zip ∘ ⟨ id , map p ⟩
    ≡⟨ cong (λ { f → concat ∘ map (proj₂ ~> f , (nilp ∘ proj₁)) ∘ uncurry zip ∘ ⟨ id , map p ⟩}) (wrapNat proj₁) ⟩
    concat ∘ map (proj₂ ~> (wrap ∘ proj₁) , (nilp ∘ proj₁)) ∘ uncurry zip ∘ ⟨ id , map p ⟩
    ≡⟨⟩
    {!!}
