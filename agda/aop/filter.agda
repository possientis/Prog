import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.List    using (List; _∷_; []; concat; map; _++_; zip)
open import Data.Product using (_×_; proj₁; proj₂; _,_; uncurry)
open import Data.Bool    using (Bool; true; false)
open import Function     using (_∘_; id)


postulate
  extensionality : ∀ {ℓ} {a b : Set ℓ} {f g : a → b}
    → (∀ (x : a) → f x ≡ g x)
      -----------------------
    →         f ≡ g

-- functor law for List: composition
∘-map : ∀ {ℓ} {a b c : Set ℓ} → {f : a → b} → {g : b → c} → map (g ∘ f) ≡ map g ∘ map f
∘-map = extensionality k
  where
    k : ∀ {ℓ} {a b c : Set ℓ} → {f : a → b} → {g : b → c} → (xs : List a) →
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

-- functor law for List: identity
id-map : ∀ {ℓ} {a : Set ℓ} → map (id {ℓ} {a}) ≡ id {ℓ} {List a}
id-map {ℓ} {a} = extensionality k
  where
    k : ∀ (xs : List a) → map id xs ≡ id xs
    k [] = refl
    k (x ∷ xs) =
      begin
        map id (x ∷ xs)
        ≡⟨⟩
        id x ∷ map id xs
        ≡⟨⟩
        x ∷ map id xs
        ≡⟨ cong (x ∷_) (k xs) ⟩
        x ∷ id xs
        ≡⟨⟩
        x ∷ xs
        ∎

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

∘-distrib-~>-r : ∀ {a b c : Set} → (p : a → Bool) -> (f g : a → b) → (h : c → a) →
  (p ~> f , g) ∘ h ≡ ((p ∘ h) ~> (f ∘ h) , (g ∘ h))
∘-distrib-~>-r {a} {b} {c} p f g h = {!!}

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

zip' : ∀ {a b : Set} → List a × List b → List (a × b)
zip' = uncurry zip

⟨_,_⟩ : ∀ {a b c : Set} → (a → b) → (a → c) → a → b × c
⟨ f , g ⟩ x = (f x , g x)


_⊕_ : ∀ {a₁ a₂ b₁ b₂ : Set} → (a₁ → b₁) → (a₂ → b₂) → a₁ × a₂ → b₁ × b₂
(f₁ ⊕ f₂) (x₁ , x₂) = (f₁ x₁ , f₂ x₂)

Δ : ∀ {a : Set} → a → a × a
Δ x = (x , x)

⊕∘Δ : ∀ {a b c : Set} → {f : a → b} → {g : a → c} → (f ⊕ g) ∘ Δ ≡ ⟨ f , g ⟩
⊕∘Δ {a} {b} {c} {f} {g} = extensionality k
  where
    k : ∀ (x : a) → ((f ⊕ g) ∘ Δ) x ≡ ⟨ f , g ⟩ x
    k x = refl

map-⊕-zip-Δ : ∀ {a b c : Set} → {f : a → b} → {g : a → c} →
  map (f ⊕ g) ∘ zip' ∘ Δ ≡ map ⟨ f , g ⟩

map-⊕-zip-Δ {a} {b} {c} {f} {g} = extensionality k
  where
    k : ∀ (xs : List a) → (map (f ⊕ g) ∘ zip' ∘ Δ) xs ≡ map ⟨ f , g ⟩ xs
    k [] = refl
    k (x ∷ xs) =
      begin
        (map (f ⊕ g) ∘ zip' ∘ Δ) (x ∷ xs)
        ≡⟨⟩
        map (f ⊕ g) (zip' (Δ (x ∷ xs)))
        ≡⟨⟩
        map (f ⊕ g) (zip' (x ∷ xs , x ∷ xs))
        ≡⟨⟩
        map (f ⊕ g) ((x , x) ∷ zip' (xs , xs))
        ≡⟨⟩
        (f ⊕ g) (x , x) ∷ map (f ⊕ g) (zip' (xs , xs))
        ≡⟨⟩
        (f x , g x) ∷ map (f ⊕ g) (zip' (Δ xs))
        ≡⟨⟩
        (f x , g x) ∷ (map (f ⊕ g) ∘ zip' ∘ Δ) xs
        ≡⟨ cong ((f x , g x) ∷_) (k xs) ⟩
        (f x , g x) ∷ map ⟨ f , g ⟩ xs
        ≡⟨⟩
        ⟨ f , g ⟩ x ∷ map ⟨ f , g ⟩ xs
        ≡⟨⟩
        map ⟨ f , g ⟩ (x ∷ xs)
        ∎

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


-- zip' is a natural transformation : (×) ∘ (List × List) ⇒ List ∘ (×)
-- zip' : List a₁ × List a₂ → List (a₁ × a₂)
zipNat : ∀ {a₁ a₂ b₁ b₂ : Set} → {f₁ : a₁ → b₁} → {f₂ : a₂ → b₂} →
  map (f₁ ⊕ f₂) ∘ zip' ≡ zip' ∘ (map f₁ ⊕ map f₂)
zipNat {a₁} {a₂} {b₁} {b₂} {f₁} {f₂} = extensionality k
  where
    k : ∀ (xs : List a₁ × List a₂) →
      (map (f₁ ⊕ f₂) ∘ zip') xs ≡ (zip' ∘ (map f₁ ⊕ map f₂)) xs
    k ([] , ys) = refl
    k (x ∷ xs , []) = refl
    k (x ∷ xs , y ∷ ys) =
      begin
        (map (f₁ ⊕ f₂) ∘ zip') (x ∷ xs , y ∷ ys)
        ≡⟨⟩
        map (f₁ ⊕ f₂) (zip' (x ∷ xs , y ∷ ys))
        ≡⟨⟩
        map (f₁ ⊕ f₂) ((x , y) ∷ zip' (xs , ys))
        ≡⟨⟩
        (f₁ ⊕ f₂) (x , y) ∷ map (f₁ ⊕ f₂) (zip' (xs , ys))
        ≡⟨⟩
        (f₁ ⊕ f₂) (x , y) ∷ (map (f₁ ⊕ f₂) ∘ zip') (xs , ys)
        ≡⟨ cong ((f₁ ⊕ f₂) (x , y) ∷_) (k ((xs , ys))) ⟩
        (f₁ ⊕ f₂) (x , y) ∷ (zip' ∘ (map f₁ ⊕ map f₂)) (xs , ys)
        ≡⟨⟩
        (f₁ ⊕ f₂) (x , y) ∷ zip' ((map f₁ ⊕ map f₂) (xs , ys))
        ≡⟨⟩
        (f₁ ⊕ f₂) (x , y) ∷ zip' (map f₁ xs , map f₂ ys)
        ≡⟨⟩
        (f₁ x , f₂ y) ∷ zip' (map f₁ xs , map f₂ ys)
        ≡⟨⟩
        zip' (f₁ x ∷ map f₁ xs , f₂ y ∷ map f₂ ys)
        ≡⟨⟩
        zip' (map f₁ (x ∷ xs) , map f₂ (y ∷ ys))
        ≡⟨⟩
        zip' ((map f₁ ⊕ map f₂) (x ∷ xs , y ∷ ys))
        ≡⟨⟩
        (zip' ∘ (map f₁ ⊕ map f₂)) (x ∷ xs , y ∷ ys)
        ∎

zipNatApp : ∀ {a b c : Set} → {f : a → b} → {g : a → c} →
  zip' ∘ ⟨ map f , map g ⟩ ≡ map ⟨ f , g ⟩

zipNatApp {a} {b} {c} {f} {g} =
  begin
    zip' ∘ ⟨ map f , map g ⟩
    ≡⟨⟩
    zip' ∘ (map f ⊕ map g) ∘ Δ
    ≡⟨ cong (_∘ Δ) (sym zipNat) ⟩
    map (f ⊕ g) ∘ zip' ∘ Δ
    ≡⟨ map-⊕-zip-Δ ⟩
    map ⟨ f , g ⟩
    ∎

L1 : ∀ {a : Set} → {p : a → Bool} →
  map proj₁ ∘ filter proj₂ ∘ zip' ∘ ⟨ id , map p ⟩ ≡ filter p

L1 {a} {p} =
  begin
    map proj₁ ∘ filter proj₂ ∘ zip' ∘ ⟨ id , map p ⟩
    -- definition of filter
    ≡⟨⟩ map proj₁
      ∘ concat
      ∘ map (proj₂ ~> wrap , nilp)
      ∘ zip'
      ∘ ⟨ id , map p ⟩
    -- concat is a natural transformation List² ⇒ List
    ≡⟨  cong (λ { f →
    f ∘ map (proj₂ ~> wrap , nilp)
      ∘ zip'
      ∘ ⟨ id , map p ⟩}) concatNat ⟩
    -- =>
        concat
      ∘ map (map proj₁)
      ∘ map (proj₂ ~> wrap , nilp)
      ∘ zip'
      ∘ ⟨ id , map p ⟩
    -- functor law for List, aka applying ∘-map
    ≡⟨  cong (λ { f → concat ∘ f ∘ zip' ∘ ⟨ id , map p ⟩ }) (sym ∘-map) ⟩
    -- =>
        concat
      ∘ map (map proj₁ ∘ (proj₂ ~> wrap , nilp))
      ∘ zip'
      ∘ ⟨ id , map p ⟩
    -- left-distributivity of ∘ over ~>
    ≡⟨  cong (λ { f →
        concat
      ∘ map f
      ∘ zip'
      ∘ ⟨ id , map p ⟩ }) (∘-distrib-~>-l proj₂ wrap nilp (map proj₁)) ⟩
    -- =>
        concat
      ∘ map (proj₂ ~> (map proj₁ ∘ wrap) , (map proj₁ ∘ nilp))
      ∘ zip'
      ∘ ⟨ id , map p ⟩
    -- nilp is a natural transformation Id ⇒ List
    ≡⟨ cong (λ { f →
       concat
      ∘ map (proj₂ ~> (map proj₁ ∘ wrap) , f)
      ∘ zip'
      ∘ ⟨ id , map p ⟩}) (nilpNat proj₁) ⟩
    -- =>
        concat
      ∘ map (proj₂ ~> (map proj₁ ∘ wrap) , (nilp ∘ proj₁))
      ∘ zip'
      ∘ ⟨ id , map p ⟩
    -- wrap is a natural transformation Id ⇒ List
    ≡⟨  cong (λ { f →
        concat
      ∘ map (proj₂ ~> f , (nilp ∘ proj₁))
      ∘ zip'
      ∘ ⟨ id , map p ⟩}) (wrapNat proj₁) ⟩
    -- =>
        concat
      ∘ map (proj₂ ~> (wrap ∘ proj₁) , (nilp ∘ proj₁))
      ∘ zip'
      ∘ ⟨ id , map p ⟩
    -- functor law for List, aka applying id-map
    ≡⟨  cong (λ { f →
        concat
      ∘ map (proj₂ ~> (wrap ∘ proj₁) , (nilp ∘ proj₁))
      ∘ zip'
      ∘ ⟨ f , map p ⟩ }) (sym id-map) ⟩
    -- =>
        concat
      ∘ map (proj₂ ~> (wrap ∘ proj₁) , (nilp ∘ proj₁))
      ∘ zip'
      ∘ ⟨ map id , map p ⟩
    -- applying zipNatApp
    ≡⟨  cong (λ { f →
        concat
      ∘ map (proj₂ ~> (wrap ∘ proj₁) , (nilp ∘ proj₁))
      ∘ f}) zipNatApp ⟩
    -- =>
        concat
      ∘ map (proj₂ ~> (wrap ∘ proj₁) , (nilp ∘ proj₁))
      ∘ map ⟨ id , p ⟩
    -- functor law for List, aka applying ∘-map
    ≡⟨  cong (concat ∘_) (sym ∘-map) ⟩
    -- =>
        concat
      ∘ map ((proj₂ ~> (wrap ∘ proj₁) , (nilp ∘ proj₁)) ∘ ⟨ id , p ⟩)
    ≡⟨⟩
    {!!}
