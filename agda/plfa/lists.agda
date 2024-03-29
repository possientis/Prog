module lists where


import Relation.Binary.PropositionalEquality as Eq

open Eq                         using (_≡_; refl; trans; sym; cong; subst)
open Eq.≡-Reasoning             using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Bool           using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat            using (ℕ; zero; suc; _≤_; z≤n; s≤s; _+_; _*_; _∸_)
open import Relation.Nullary    using (Dec; yes; no; ¬_)
open import Data.Nat.Properties using (+-assoc; +-suc; +-comm
                                      ;*-distribʳ-+; *-distribˡ-+
                                      ;*-comm; +-identityˡ; +-identityʳ
                                      ;*-assoc; *-identityˡ; *-identityʳ)
open import Data.Product        using (_×_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum            using (_⊎_; inj₁; inj₂)
open import Function            using (_∘_)
open import Level               using (Level)
open import isomorphism         using (_≃_; _⇔_)

open import Data.Product        using () renaming (_,_ to ⟨_,_⟩)

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
++-assoc {a} [] ys zs = refl
++-assoc {a} (x ∷ xs) ys zs =
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

++-identityˡ : ∀ {a : Set} → (xs : List a) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {a : Set} → (xs : List a) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
    ≡⟨⟩
    x ∷ (xs ++ [])
    ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
    ∎

length : ∀ {a : Set} → List a → ℕ
length [] = zero
length (_ ∷ xs) = suc (length xs)

_ : length [ 0 , 1  , 2 ] ≡ 3
_ =
  begin
    length [ 0 , 1 , 2 ]
    ≡⟨⟩
    length (0 ∷ 1 ∷ 2 ∷ [])
    ≡⟨⟩
    suc (length (1 ∷ 2 ∷ []))
    ≡⟨⟩
    suc (suc (length (2 ∷ [])))
    ≡⟨⟩
    suc (suc (suc (length {ℕ} [])))
    ≡⟨⟩
    suc (suc (suc 0))
    ≡⟨⟩
    3
    ∎

length-++ : ∀ {a : Set} → (xs ys : List a) →
  length (xs ++ ys) ≡ length xs + length ys

length-++ [] ys = refl
length-++ (x ∷ xs) ys =
  begin
    length ((x ∷ xs) ++ ys)
    ≡⟨⟩
    length (x ∷ (xs ++ ys))
    ≡⟨⟩
    suc (length (xs ++ ys))
    ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
    ≡⟨⟩
    (suc (length xs)) + length ys
    ≡⟨⟩
    length (x ∷ xs) + length ys
    ∎

reverse : ∀ {a : Set} → List a → List a
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

_ : reverse [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse [ 0 , 1 , 2 ]
    ≡⟨⟩
    reverse (0 ∷ 1 ∷ 2 ∷ [])
    ≡⟨⟩
    reverse (1 ∷ 2 ∷ []) ++ [ 0 ]
    ≡⟨⟩
    (reverse (2 ∷ []) ++ [ 1 ]) ++ [ 0 ]
    ≡⟨⟩
    ((reverse [] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
    ≡⟨⟩
    (([] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
    ≡⟨⟩
    ([ 2 ] ++ [ 1 ]) ++ [ 0 ]
    ≡⟨⟩
    ((2 ∷ []) ++ [ 1 ]) ++ [ 0 ]
    ≡⟨⟩
    (2 ∷ ([] ++ [ 1 ])) ++ [ 0 ]
    ≡⟨⟩
    (2 ∷ [ 1 ]) ++ [ 0 ]
    ≡⟨⟩
    2 ∷ ([ 1 ] ++ [ 0 ])
    ≡⟨⟩
    2 ∷ ((1 ∷ []) ++ [ 0 ])
    ≡⟨⟩
    2 ∷ (1 ∷ ([] ++ [ 0 ]))
    ≡⟨⟩
    2 ∷ (1 ∷ [ 0 ])
    ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
    ≡⟨⟩
    [ 2 , 1 , 0 ]
    ∎

reverse++distrib : ∀ {a : Set} → {xs ys : List a} →
  reverse (xs ++ ys) ≡ reverse ys ++ reverse xs

reverse++distrib {a} {[]} {ys} = sym (++-identityʳ (reverse ys))
reverse++distrib {a} {(x ∷ xs)} {ys} =
  begin
    reverse ((x ∷ xs) ++ ys)
    ≡⟨⟩
    reverse (x ∷ (xs ++ ys))
    ≡⟨⟩
    reverse (xs ++ ys) ++ [ x ]
    ≡⟨ cong (_++ [ x ]) (reverse++distrib {a} {xs}) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
    ≡⟨ ++-assoc (reverse ys) _ _  ⟩
    reverse ys ++ (reverse xs ++ [ x ])
    ≡⟨⟩
    reverse ys ++ reverse (x ∷ xs)
    ∎

reverse-involutive : ∀ {a : Set} → {xs : List a} → reverse (reverse xs) ≡ xs
reverse-involutive {a} {[]} = refl
reverse-involutive {a} {x ∷ xs} =
  begin
    reverse (reverse (x ∷ xs))
    ≡⟨⟩
    reverse (reverse xs ++ [ x ])
    ≡⟨ reverse++distrib {a} {reverse xs} ⟩
    reverse [ x ] ++ reverse (reverse xs)
    ≡⟨⟩
    [ x ] ++ reverse (reverse xs)
    ≡⟨ cong ([ x ] ++_) reverse-involutive ⟩
    [ x ] ++ xs
    ≡⟨⟩
    x ∷ xs
    ∎

shunt : ∀ {a : Set} → List a → List a → List a
shunt [] ys = ys
shunt (x ∷ xs) ys =  shunt xs (x ∷ ys)

shunt-reverse : ∀ {a : Set} → {xs ys : List a} →
  shunt xs ys ≡ reverse xs ++ ys
shunt-reverse {a} {[]} {_}= refl
shunt-reverse {a} {x ∷ xs} {ys} =
  begin
    shunt (x ∷ xs) ys
    ≡⟨⟩
    shunt xs (x ∷ ys)
    ≡⟨ shunt-reverse {a} {xs} ⟩
    reverse xs ++ (x ∷ ys)
    ≡⟨⟩
    reverse xs ++ ([ x ] ++ ys)
    ≡⟨ sym (++-assoc (reverse xs) _ _) ⟩
    (reverse xs ++ [ x ]) ++ ys
    ≡⟨⟩
    reverse (x ∷ xs) ++ ys
    ∎

reverse' : ∀ {a : Set} → List a → List a
reverse' xs = shunt xs []

reverses : ∀ {a : Set} → {xs : List a} →
  reverse' xs ≡ reverse xs
reverses {a} {xs} =
  begin
    reverse' xs
    ≡⟨⟩
    shunt xs []
    ≡⟨ shunt-reverse {a} {xs} ⟩
    reverse xs ++ []
    ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
    ∎

_ : reverse' [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse' [ 0 , 1 , 2 ]
    ≡⟨⟩
    shunt [ 0 , 1 , 2 ] []
    ≡⟨⟩
    shunt [ 1 , 2 ] [ 0 ]
    ≡⟨⟩
    shunt [ 2 ] [ 1 , 0 ]
    ≡⟨⟩
    shunt [] [ 2 , 1 , 0 ]
    ≡⟨⟩
    [ 2 , 1 , 0 ]
    ∎

map : ∀ {a b : Set} → (a → b) → List a → List b
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

_ : map suc [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    map suc [ 0 , 1 , 2 ]
    ≡⟨⟩
     1 ∷ map suc [ 1 , 2 ]
     ≡⟨⟩
     1 ∷ 2 ∷ map suc [ 2 ]
     ≡⟨⟩
     1 ∷ 2 ∷ 3 ∷ []
     ≡⟨⟩
     [ 1 , 2 , 3 ]
     ∎

sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    sucs [ 0 , 1 , 2 ]
    ≡⟨⟩
    map suc [ 0 , 1 , 2 ]
    ≡⟨⟩
    [ 1 , 2 , 3 ]
    ∎

postulate
  extensionality : ∀ {a b : Set} → {f g : a → b} →
    (∀ (x : a) → f x ≡ g x) → f ≡ g

postulate
  extensionalityDep : ∀ {a : Set} {b : a → Set} {f g : ∀ (x : a) → b x} →
    (∀ (x : a) → f x ≡ g x) → f ≡ g


map-compose : ∀ {a b c : Set} → {f : a → b} → {g : b → c} →
  map (g ∘ f) ≡ map g ∘ map f
map-compose {a} {b} {c} {f} {g} = extensionality k
  where
    k : ∀ (xs : List a) → map (g ∘ f) xs ≡ (map g ∘ map f) xs
    k [] = refl
    k (x ∷ xs) =
      begin
        map (g ∘ f) (x ∷ xs)
        ≡⟨⟩
        (g ∘ f) x ∷ map (g ∘ f) xs
        ≡⟨ cong ((g ∘ f) x ∷_) (k xs) ⟩
        (g ∘ f) x ∷ (map g ∘ map f) xs
        ≡⟨⟩
        g (f x) ∷ map g (map f xs)
        ≡⟨⟩
        map g (f x ∷ map f xs)
        ≡⟨⟩
        map g (map f (x ∷ xs))
        ≡⟨⟩
        (map g ∘ map f) (x ∷ xs)
        ∎

map-++-distribute : ∀ {a b : Set} → {f : a → b} → {xs ys : List a} →
  map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute {a} {b} {f} {[]} {ys} = refl
map-++-distribute {a} {b} {f} {x ∷ xs} {ys} =
  begin
    map f ((x ∷ xs) ++ ys)
    ≡⟨⟩
    map f (x ∷ xs ++ ys)
    ≡⟨⟩
    f x ∷ map f (xs ++ ys)
    ≡⟨ cong (f x ∷_) (map-++-distribute {a} {b} {f} {xs}) ⟩
    f x ∷ map f xs ++ map f ys
    ≡⟨⟩
    (f x ∷ map f xs) ++ map f ys
    ≡⟨⟩
    map f (x ∷ xs) ++ map f ys
    ∎

-- leafs of type a, nodes of type b
data Tree (a b : Set) : Set where
  leaf : a → Tree a b
  node : Tree a b → b → Tree a b → Tree a b


mapTree : ∀ {a b c d : Set} → (a → c) → (b → d) → Tree a b → Tree c d
mapTree f g (leaf x) = leaf (f x)
mapTree f g (node tₗ x tᵣ) = node (mapTree f g tₗ) (g x) (mapTree f g tᵣ)

foldr : ∀ {a b : Set} → (a → b → b) → b → List a → b
foldr _⊗_ e [] = e
foldr _⊗_ e (x ∷ xs) = x ⊗ foldr _⊗_ e xs

_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    foldr _+_ 0 [ 1 , 2 , 3 , 4 ]
    ≡⟨⟩
    1 + foldr _+_ 0 [ 2 , 3 , 4 ]
    ≡⟨⟩
    1 + (2 + foldr _+_ 0 [ 3 , 4 ])
    ≡⟨⟩
    1 + (2 + (3 + foldr _+_ 0 [ 4 ]))
    ≡⟨⟩
    1 + (2 + (3 + (4 + foldr _+_ 0 [])))
    ≡⟨⟩
    1 + (2 + (3 + (4 + 0)))
    ≡⟨⟩
    10
    ∎

sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    sum [ 1 , 2 , 3 , 4 ]
    ≡⟨⟩
    foldr _+_ 0 [ 1 , 2 , 3 , 4 ]
    ≡⟨⟩
    10
    ∎

product : List ℕ → ℕ
product = foldr _*_ 1

_ : product [ 1 , 2 , 3 , 4 ] ≡ 24
_ = refl

foldr-++ : ∀ {a b : Set} {_⊗_ : a → b → b} {e : b} (xs ys : List a) →
  foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs

foldr-++ {a} {b} {_⊗_} {e} [] ys = refl
foldr-++ {a} {b} {_⊗_} {e} (x ∷ xs) ys =
  begin
    foldr _⊗_ e ((x ∷ xs) ++ ys)
    ≡⟨⟩
    foldr _⊗_ e (x ∷ (xs ++ ys))
    ≡⟨⟩
    x ⊗ foldr _⊗_ e (xs ++ ys)
    ≡⟨ cong (x ⊗_) (foldr-++ xs ys) ⟩
    x ⊗ foldr _⊗_ (foldr _⊗_ e ys) xs
    ≡⟨⟩
    foldr _⊗_ (foldr _⊗_ e ys) (x ∷ xs)
    ∎

foldr-∷ : ∀ {a : Set} → {xs : List a} →
  foldr _∷_ [] xs ≡ xs
foldr-∷ {a} {[]} = refl
foldr-∷ {a} {x ∷ xs} =
  begin
    foldr _∷_ [] (x ∷ xs)
    ≡⟨⟩
    x ∷ foldr _∷_ [] xs
    ≡⟨ cong (x ∷_) foldr-∷ ⟩
    x ∷ xs
    ∎

map-is-foldr : ∀ {a b : Set} → {f : a → b} →
  map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr {a} {b} {f} = extensionality k
  where
    _⊗_ : a → List b → List b
    x ⊗ xs = f x ∷ xs
    k : ∀ (xs : List a) → map f xs ≡ foldr _⊗_ [] xs
    k [] = refl
    k (x ∷ xs) =
      begin
        map f (x ∷ xs)
        ≡⟨⟩
        f x ∷ map f xs
        ≡⟨⟩
        x ⊗ (map f xs)
        ≡⟨ cong (x ⊗_) (k xs) ⟩
        x ⊗ foldr _⊗_ [] xs
        ≡⟨⟩
        foldr _⊗_ [] (x ∷ xs)
        ∎

foldTree : ∀ {a b c : Set} → (a → c) → (c → b → c → c) → Tree a b → c
foldTree f g (leaf x) = f x
foldTree f g (node tₗ x tᵣ) = g (foldTree f g tₗ) x (foldTree f g tᵣ)


TreeRec : ∀ {a b : Set} → (c : ∀ (t : Tree a b) → Set) →
  (∀ (x : a) → c (leaf x)) →
  (∀ (x : b) (tₗ tᵣ : Tree a b) → c tₗ → c tᵣ → c (node tₗ x tᵣ)) →
  (∀ (t : Tree a b) → c t)
TreeRec c Hl Hn (leaf x) = Hl x
TreeRec c Hl Hn (node tₗ x tᵣ) = Hn x tₗ tᵣ (TreeRec c Hl Hn tₗ) (TreeRec c Hl Hn tᵣ)

-- foldTree is a specializarion of the recursor TreeRec
foldTreeSpec : ∀ {a b c : Set} → (f : a → c) → (g : c → b → c → c) → (t : Tree a b) →
  foldTree f g t ≡ TreeRec (λ _ → c) f (λ x _ _ cₗ cᵣ → g cₗ x cᵣ) t
foldTreeSpec f g (leaf x) = refl
foldTreeSpec {a} {b} {c} f g (node tₗ x tᵣ) =
  begin
    foldTree f g (node tₗ x tᵣ)
    ≡⟨⟩
    g (foldTree f g tₗ) x (foldTree f g tᵣ)
    ≡⟨ cong (λ u → g u x (foldTree f g tᵣ)) (foldTreeSpec f g tₗ) ⟩
    g (TreeRec (λ _ → c) f (λ x _ _ cₗ cᵣ → g cₗ x cᵣ) tₗ) x (foldTree f g tᵣ)
    ≡⟨ cong
       (λ u → g (TreeRec (λ _ → c) f (λ x _ _ cₗ cᵣ → g cₗ x cᵣ) tₗ) x u)
       (foldTreeSpec f g tᵣ)
     ⟩
    g (TreeRec (λ _ → c) f (λ x _ _ cₗ cᵣ → g cₗ x cᵣ) tₗ) x
      (TreeRec (λ _ → c) f (λ x _ _ cₗ cᵣ → g cₗ x cᵣ) tᵣ)
    ≡⟨⟩
    TreeRec (λ _ → c) f (λ x _ _ cₗ cᵣ → g cₗ x cᵣ) (node tₗ x tᵣ)
    ∎

map-is-foldTree : ∀ {a b c d : Set} → {f : a → c} → {g : b → d} →
  mapTree f g ≡ foldTree (leaf ∘ f) (λ tₗ y tᵣ → node tₗ (g y) tᵣ)
map-is-foldTree {a} {b} {c} {d} {f} {g} = extensionality k
  where
    h : Tree c d → b → Tree c d → Tree c d
    h t₁ y t₂ = node t₁ (g y) t₂

    k : ∀ (t : Tree a b) →
      mapTree f g t ≡ foldTree (leaf ∘ f) h t
    k (leaf x) = refl
    k (node tₗ y tᵣ) =
      begin
        mapTree f g (node tₗ y tᵣ)
        ≡⟨⟩
        node (mapTree f g tₗ) (g y) (mapTree f g tᵣ)
        ≡⟨ cong (λ t → node t (g y) (mapTree f g tᵣ)) (k tₗ) ⟩
        node (foldTree (leaf ∘ f) h tₗ) (g y) (mapTree f g tᵣ)
        ≡⟨ cong (λ t → node (foldTree (leaf ∘ f) h tₗ) (g y) t) (k tᵣ) ⟩
        node (foldTree (leaf ∘ f) h tₗ) (g y) (foldTree (leaf ∘ f) h tᵣ)
        ≡⟨⟩
        foldTree (leaf ∘ f) h (node tₗ y tᵣ)
        ∎


downFrom : ℕ → List ℕ
downFrom zero = []
downFrom (suc n) = n ∷ downFrom n

_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl

L1 : ∀ {n : ℕ} → n * (2 + (n ∸ 1)) ≡ suc n * n
L1 {zero} = refl
L1 {suc n} =
  begin
    suc n * (2 + (suc n ∸ 1))
    ≡⟨⟩
    suc n * (2 + n)
    ≡⟨ *-comm (suc n) (2 + n) ⟩
    (2 + n) * suc n
    ≡⟨⟩
    suc (suc n) * suc n
    ∎

sumDownFrom : ∀ {n : ℕ} → sum (downFrom n) * 2 ≡ n * (n ∸ 1)  -- \.-
sumDownFrom {zero} = refl
sumDownFrom {suc n} =
  begin
    sum (downFrom (suc n)) * 2
    ≡⟨⟩
    sum (n ∷ downFrom n) * 2
    ≡⟨⟩
    (n + sum (downFrom n)) * 2
    ≡⟨ *-distribʳ-+ 2 n (sum (downFrom n)) ⟩
    n * 2 + sum (downFrom n) * 2
    ≡⟨ cong (λ { x → n * 2 + x }) (sumDownFrom {n}) ⟩
    n * 2 + n * (n ∸ 1)
    ≡⟨ sym (*-distribˡ-+ n 2 (n ∸ 1)) ⟩
    n * (2 + (n ∸ 1))
    ≡⟨ L1 {n} ⟩
    suc n * n
    ≡⟨⟩
    suc n * (suc n ∸ 1)
    ∎

record IsMonoid (a : Set) (_⊗_ : a → a → a) (e : a) : Set where
  field
    assoc : ∀ (x y z : a) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : a) → e ⊗ x ≡ x
    identityʳ : ∀ (x : a) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid ℕ _+_ 0
+-monoid =  record
  { assoc = +-assoc
  ; identityˡ = +-identityˡ
  ; identityʳ = +-identityʳ
  }

*-monoid : IsMonoid ℕ _*_ 1
*-monoid = record
  { assoc = *-assoc
  ; identityˡ = *-identityˡ
  ; identityʳ = *-identityʳ
  }

++-monoid : ∀ {a : Set} → IsMonoid (List a) _++_ []
++-monoid = record
  { assoc = ++-assoc
  ; identityˡ = ++-identityˡ
  ; identityʳ = ++-identityʳ
  }

foldr-monoid : ∀ {a : Set} {_⊗_ : a → a → a} {e : a} → IsMonoid a _⊗_ e →
  ∀ (xs : List a) (y : a) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid {a} {_⊗_} {e} ⊗-monoid [] y =
  begin
    foldr {a} {a} _⊗_ y []
    ≡⟨⟩
    y
    ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    e ⊗ y
    ≡⟨⟩
    foldr _⊗_ e [] ⊗ y
    ∎
foldr-monoid {a} {_⊗_} {e} ⊗-monoid (x ∷ xs) y
  = begin
      foldr {a} {a} _⊗_ y (x ∷ xs)
      ≡⟨⟩
      x ⊗ foldr _⊗_ y xs
      ≡⟨ cong (x ⊗_) (foldr-monoid {a} {_⊗_} {e} ⊗-monoid xs y) ⟩
      x ⊗ (foldr _⊗_ e xs ⊗ y)
      ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
      (x ⊗ foldr _⊗_ e xs) ⊗ y
      ≡⟨⟩
      foldr _⊗_ e (x ∷ xs) ⊗ y
      ∎

foldr-monoid-++ : ∀ {a : Set} (_⊗_ : a → a → a) (e : a) → IsMonoid a _⊗_ e →
  ∀ (xs ys : List a) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ {a} _⊗_ e ⊗-monoid xs ys =
  begin
    foldr _⊗_ e (xs ++ ys)
    ≡⟨ foldr-++ xs ys  ⟩
    foldr _⊗_ (foldr _⊗_ e ys) xs
    ≡⟨ foldr-monoid ⊗-monoid xs (foldr _⊗_ e ys) ⟩
    foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
    ∎

foldl : ∀ {a b : Set} → (b → a → b) → b → List a → b
foldl _⊗_ y [] = y
foldl _⊗_ y (x ∷ xs) = foldl _⊗_ (y ⊗ x) xs

L2 : ∀ {a : Set} (_⊗_ : a → a → a) (e : a) (x y z : a) →
  foldr _⊗_ e [ x , y , z ] ≡ x ⊗ (y ⊗ (z ⊗ e))
L2 _⊗_ e x y z =
  begin
    foldr _⊗_ e [ x , y , z ]
    ≡⟨⟩
    x ⊗ foldr _⊗_ e [ y , z ]
    ≡⟨⟩
    x ⊗ (y ⊗ foldr _⊗_ e [ z ])
    ≡⟨⟩
    x ⊗ (y ⊗ (z ⊗ foldr _⊗_ e []))
    ≡⟨⟩
    x ⊗ (y ⊗ (z ⊗ e))
    ∎

L3 : ∀ {a : Set} (_⊗_ : a → a → a) (e : a) (x y z : a) →
  foldl _⊗_ e [ x , y , z ] ≡ ((e ⊗ x) ⊗ y) ⊗ z
L3 _⊗_ e x y z =
  begin
    foldl _⊗_ e [ x , y , z ]
    ≡⟨⟩
    foldl _⊗_ (e ⊗ x) [ y , z ]
    ≡⟨⟩
    foldl _⊗_ ((e ⊗ x) ⊗ y) [ z ]
    ≡⟨⟩
    foldl _⊗_ (((e ⊗ x) ⊗ y) ⊗ z) []
    ≡⟨⟩
    ((e ⊗ x) ⊗ y) ⊗ z
    ∎

⊗-foldl : ∀ {a : Set} (_⊗_ : a → a → a) (e : a) → IsMonoid a _⊗_ e →
  ∀ (y' y : a) (xs : List a) → y' ⊗ foldl _⊗_ y xs ≡ foldl _⊗_ (y' ⊗ y) xs
⊗-foldl _⊗_ e ⊗-monoid y' y [] =
  begin
    y' ⊗ foldl _⊗_ y []
    ≡⟨⟩
    y' ⊗ y
    ≡⟨⟩
    foldl _⊗_ (y' ⊗ y) []
    ∎
⊗-foldl _⊗_ e ⊗-monoid y' y (x ∷ xs) =
  begin
    y' ⊗ foldl _⊗_ y (x ∷ xs)
    ≡⟨⟩
    y' ⊗ foldl _⊗_ (y ⊗ x) xs
    ≡⟨ ⊗-foldl _⊗_ e ⊗-monoid y' (y ⊗ x) xs ⟩
    foldl _⊗_ (y' ⊗ (y ⊗ x)) xs
    ≡⟨ cong (λ { u → foldl _⊗_ u xs }) (sym (assoc ⊗-monoid y' y x)) ⟩
    foldl _⊗_ ((y' ⊗ y) ⊗ x) xs
    ≡⟨⟩
    foldl _⊗_ (y' ⊗ y) (x ∷ xs)
    ∎

foldr-monoid-foldl : ∀ {a : Set} (_⊗_ : a → a → a) (e :  a) → IsMonoid a _⊗_ e →
  ∀ (xs : List a) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
foldr-monoid-foldl _⊗_ e ⊗-monoid [] = refl
foldr-monoid-foldl _⊗_ e ⊗-monoid (x ∷ xs) =
  begin
    foldr _⊗_ e (x ∷ xs)
    ≡⟨⟩
    x ⊗ foldr _⊗_ e xs
    ≡⟨ cong (x ⊗_) (foldr-monoid-foldl _⊗_ e ⊗-monoid xs) ⟩
    x ⊗ foldl _⊗_ e xs
    ≡⟨ ⊗-foldl _⊗_ e ⊗-monoid x e xs ⟩
    foldl _⊗_ (x ⊗ e) xs
    ≡⟨ cong (λ{u → foldl _⊗_ u xs}) (identityʳ ⊗-monoid x) ⟩
    foldl _⊗_ x xs
    ≡⟨ cong (λ { u → foldl _⊗_ u xs }) (sym (identityˡ ⊗-monoid x)) ⟩
    foldl _⊗_ (e ⊗ x) xs
    ≡⟨⟩
    foldl _⊗_ e (x ∷ xs)
    ∎

-- reusing the name of constructors for List appears to be fine
data All {a : Set} (p : a → Set) : List a → Set where
  []  : All p []
  _∷_ : ∀ {x : a} {xs : List a} → p x → All p xs → All p (x ∷ xs)


_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []

data Any {a : Set} (p : a → Set) : List a → Set where
  here  : ∀ {x : a} {xs : List a} → p x → Any p (x ∷ xs)
  there : ∀ {x : a} {xs : List a} → Any p xs → Any p (x ∷ xs)

infix 4 _∈_ _∉_

_∈_ : ∀ {a : Set} (x : a) (xs : List a) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {a : Set} (x : a) (xs : List a) → Set
x ∉ xs = ¬ (x ∈ xs)


_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = here refl

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (here refl))

not-in : 3 ∉ [ 0 , 1 , 0 , 2 ]
not-in (there (there (there (here ()))))
not-in (there (there (there (there ()))))

All-++-⇔ : ∀ {a : Set} {p : a → Set} (xs ys : List a) →
  All p (xs ++ ys) ⇔ (All p xs × All p ys)
All-++-⇔ xs ys = record
  { to = to xs ys
  ; from = from xs ys
  }
  where
  to : ∀ {a : Set} {p : a → Set}(xs ys : List a) →
    All p (xs ++ ys) → All p xs × All p ys
  to [] ys = λ {p → ⟨ [] , p ⟩ }
  to (x ∷ xs) ys (p ∷ q) with to xs ys q
  ... | ⟨ fst , snd ⟩ = ⟨ p ∷ fst , snd ⟩

  from : ∀ {a : Set} {p : a → Set}(xs ys : List a) →
    All p xs × All p ys → All p (xs ++ ys)
  from [] ys = λ{⟨ _ , x ⟩ → x}
  from (x ∷ xs) ys ⟨ p ∷ fst , snd ⟩ = p ∷ from xs ys ⟨ fst , snd ⟩


Any-++-⇔ : ∀ {a : Set} {p : a → Set} (xs ys : List a) →
  Any p (xs ++ ys) ⇔ (Any p xs ⊎ Any p ys)
Any-++-⇔ xs ys = record
  { to = to xs ys
  ; from = from xs ys
  }
  where
  to : ∀ {a : Set} {p : a → Set} (xs ys : List a) →
    Any p (xs ++ ys) → (Any p xs ⊎ Any p ys)
  to [] ys q = inj₂ q
  to (x ∷ xs) ys (here q) = inj₁ (here q)
  to (x ∷ xs) ys (there q) with to xs ys q
  ... | inj₁ r = inj₁ (there r)
  ... | inj₂ r = inj₂ r

  from : ∀ {a : Set} {p : a → Set} (xs ys : List a) →
    (Any p xs ⊎ Any p ys) → Any p (xs ++ ys)
  from [] ys (inj₂ q) = q
  from (x ∷ xs) ys (inj₁ (here q)) = here q
  from (x ∷ xs) ys (inj₁ (there q)) = there (from xs ys (inj₁ q))
  from (x ∷ xs) ys (inj₂ q) = there (from xs ys (inj₂ q))


All-++-≃ : ∀ {a : Set} {p : a → Set} (xs ys : List a) →
  All p (xs ++ ys) ≃ All p xs × All p ys
All-++-≃ xs ys = record
  { to = to xs ys
  ; from = from xs ys
  ; from∘to = from∘to xs ys
  ; to∘from = to∘from xs ys
  }
  where
    to : ∀ {a : Set} {p : a → Set} (xs ys : List a) →
      All p (xs ++ ys) → All p xs × All p ys
    to [] ys q = ⟨ [] , q ⟩
    to (x ∷ xs) ys (q ∷ r) with to xs ys r
    ... | ⟨ fst , snd ⟩ = ⟨ q ∷ fst , snd ⟩

    from : ∀ {a : Set} {p : a → Set} (xs ys : List a) →
      All p xs × All p ys → All p (xs ++ ys)
    from [] ys ⟨ [] , q ⟩ = q
    from (x ∷ xs) ys ⟨ q ∷ r , s ⟩ = q ∷ from xs ys ⟨ r , s ⟩

    from∘to : ∀ {a : Set} {p : a → Set} (xs ys : List a) (q : All p (xs ++ ys)) →
      from xs ys (to xs ys q) ≡ q
    from∘to [] ys q = refl
    from∘to (x ∷ xs) ys (q ∷ r) = cong (q ∷_) (from∘to xs ys r)

    to∘from : ∀ {a : Set} {p : a → Set} (xs ys : List a) (q : All p xs × All p ys) →
      to xs ys (from xs ys q) ≡ q
    to∘from [] ys ⟨ [] , q ⟩ = refl
    to∘from (x ∷ xs) ys ⟨ q ∷ r , s ⟩ with to∘from xs ys ⟨ r , s ⟩
    ... | k with to xs ys (from xs ys ⟨ r , s ⟩)
    ... | ⟨ fst , snd ⟩ = cong (λ { x → ⟨ q ∷ proj₁ x , proj₂ x ⟩ }) k

¬Any⇔All¬ : ∀ {a : Set} {p : a → Set} (xs : List a) →
  (¬_ ∘ Any p) xs ⇔ All (¬_ ∘ p) xs
¬Any⇔All¬ xs = record { to = to xs ; from = from xs }
  where
  to : ∀ {a : Set} {p : a → Set} (xs : List a) → (¬ Any p xs) → All (λ x → ¬ p x) xs
  to [] f = []
  to (x ∷ xs) f =  (λ{px → f (here px)}) ∷ to xs (λ{h → f (there h)})

  from : ∀ {a : Set} {p : a → Set} (xs : List a) → All (λ x → ¬ p x) xs → ¬ Any p xs
  from (x ∷ xs) (q ∷ r) (here s) = q s
  from (x ∷ xs) (q ∷ r) (there s) = from xs r s

¬Any≃All¬ : ∀ {a : Set} {p : a → Set} (xs : List a) →
  (¬_ ∘ Any p) xs ≃ All (¬_ ∘ p) xs
¬Any≃All¬ xs = record
  { to = to xs
  ; from = from xs
  ; from∘to = from∘to xs
  ; to∘from = to∘from xs
  }
  where
  to : ∀ {a : Set} {p : a → Set} (xs : List a) → (¬ Any p xs) → All (λ x → ¬ p x) xs
  to [] f = []
  to (x ∷ xs) f =  (λ{px → f (here px)}) ∷ to xs (λ{h → f (there h)})

  from : ∀ {a : Set} {p : a → Set} (xs : List a) → All (λ x → ¬ p x) xs → ¬ Any p xs
  from (x ∷ xs) (q ∷ r) (here s) = q s
  from (x ∷ xs) (q ∷ r) (there s) = from xs r s

  k : ∀ {a : Set} {p : a → Set} (xs : List a) (q : ¬ Any p xs) (r : Any p xs) →
    from xs (to xs q) r ≡ q r
  k (x ∷ xs) q (here r) = refl
  k (x ∷ xs) q (there r) = k xs (q ∘ there) r

  from∘to : ∀ {a : Set} {p : a → Set} (xs : List a) (q : ¬ Any p xs) →
    from xs (to xs q) ≡ q
  from∘to xs q = extensionality (k xs q)

  to∘from : ∀ {a : Set} {p : a → Set} (xs : List a) (q : All (¬_ ∘ p) xs) →
    to xs (from xs q) ≡ q
  to∘from [] [] = refl
  to∘from (x ∷ xs) (q ∷ r) = cong (q ∷_) (to∘from xs r)

L4 : ∀ {a : Set} {p : a → Set} (xs : List a) (f g : ∀ (x : a) → x ∈ xs → p x) →
  (∀ (x : a) (q : x ∈ xs) → f x q ≡ g x q) → f ≡ g
L4 xs f g h = extensionalityDep (λ{x → extensionality (λ{q → h x q})})

All-∀ : ∀ {a : Set} {p : a → Set} (xs : List a) →
  All p xs ≃ ∀ (x : a) → x ∈ xs → p x
All-∀ xs = record
  { to = to xs
  ; from = from xs
  ; from∘to = from∘to xs
  ; to∘from = to∘from xs
  }
  where
  to : ∀ {a : Set} {p : a → Set} (xs : List a) →
    All p xs → ∀ (x : a) → x ∈ xs → p x
  to [] _ q ()
  to (x ∷ xs) (q ∷ r) _ (here s) = subst _ (sym s) q
  to (x ∷ xs) (q ∷ r) _ (there s) = to xs r _ s

  from : ∀ {a : Set} {p : a → Set} (xs : List a) →
    (∀ (x : a) → x ∈ xs → p x) → All p xs
  from [] _ = []
  from (x ∷ xs) f = f _ (here refl) ∷ from xs λ{_ q → f _ (there q)}

  from∘to : ∀ {a : Set} {p : a → Set} (xs : List a) (q : All p xs) →
    from xs (to xs q) ≡ q
  from∘to [] [] = refl
  from∘to (x ∷ xs) (q ∷ r) = cong (q ∷_) (from∘to xs r)

  -- This was difficult
  to∘from : ∀ {a : Set} {p : a → Set} (xs : List a) (f : ∀(x : a) → x ∈ xs → p x) →
    to xs (from xs f) ≡ f
  to∘from xs f = L4 xs _ f (k xs f)
    where
    k : ∀ {a : Set} {p : a → Set} (xs : List a) (f : ∀(x : a) → x ∈ xs → p x) (x : a) (q : x ∈ xs) →
      to xs (from xs f) x q ≡ f x q
    k (y ∷ xs) f .y (here refl) = refl
    k (y ∷ xs) f x (there q) =
      begin
        to (y ∷ xs) (from (y ∷ xs) f) x (there q)
        ≡⟨⟩
        to (y ∷ xs) (f _ (here refl) ∷ from xs λ{_ r → f _ (there r)}) x (there q)
        ≡⟨⟩
        to xs (from xs λ{_ r → f _ (there r)}) _ q
        ≡⟨ k xs (λ{u r → f u (there r)}) x q ⟩
        f x (there q)
        ∎

Any-∃ : ∀ {a : Set} {p : a → Set} (xs : List a) →
  Any p xs ≃ ∃[ x ] (x ∈ xs × p x)
Any-∃ xs = record
  { to = to xs
  ; from = from xs
  ; from∘to = from∘to xs
  ; to∘from = to∘from xs
  }
  where
  to : ∀ {a : Set} {p : a → Set} (xs : List a) →
    Any p xs → ∃[ x ] (x ∈ xs × p x)
  to (x ∷ xs) (here q) = ⟨ x , ⟨ here refl , q ⟩ ⟩
  to (x ∷ xs) (there q) with to xs q
  ... | ⟨ y , ⟨ iny , py ⟩ ⟩ = ⟨ y , ⟨ there iny , py ⟩ ⟩

  from : ∀ {a : Set} {p : a → Set} (xs : List a) →
    ∃[ x ] (x ∈ xs × p x) → Any p xs
  from [] ()
  from (x ∷ xs) ⟨ y , ⟨ here q , py ⟩ ⟩ = here (subst _ q py)
  from (x ∷ xs) ⟨ y , ⟨ there q , py ⟩ ⟩ = there (from xs ⟨ y , ⟨ q , py ⟩ ⟩)

  from∘to : ∀ {a : Set} {p : a → Set} (xs : List a) (q : Any p xs) →
    from xs (to xs q) ≡ q
  from∘to (x ∷ xs) (here q) = refl
  from∘to (x ∷ xs) (there q) = cong there (from∘to xs q)

  -- This was difficult
  to∘from : ∀ {a : Set} {p : a → Set} (xs : List a) (q : ∃[ x ] (x ∈ xs × p x)) →
    to xs (from xs q) ≡ q
  to∘from (x ∷ xs) ⟨ .x , ⟨ here refl , py ⟩ ⟩ = refl
  to∘from {a} {p} (x ∷ xs) ⟨ y , ⟨ there q , py ⟩ ⟩ with to∘from {a} {p} xs ⟨ y , ⟨ q , py ⟩ ⟩
  ... | k with to {a} {p} xs (from xs ⟨ y , ⟨ q , py ⟩ ⟩)
  ... | ⟨ y' , ⟨ q' , py' ⟩ ⟩ = cong (λ { ⟨ x , ⟨ r , s ⟩ ⟩ → ⟨ x , ⟨ there r , s ⟩ ⟩ }) k

all : ∀ {a : Set} → (a → Bool) → List a → Bool
all p xs = foldr _∧_ true (map p xs)

Decidable : ∀ {a : Set} → (a → Set) → Set
Decidable {a} p = ∀ (x : a) → Dec (p x)

All? : ∀  {a : Set} {p : a → Set} → Decidable p → Decidable (All p)
All? q [] = yes []
All? q (x ∷ xs) with q x | All? q xs
... | yes r | yes s  = yes (r ∷ s)
... | no r  | yes s  = no (λ{(k ∷ ks) → r k})
... | _     | no s   = no (λ{(k ∷ ks) →  s ks})

Any? : ∀ {a : Set} {p : a → Set} → Decidable p → Decidable (Any p)
Any? q [] = no (λ ())
Any? q (x ∷ xs) with q x | Any? q xs
... | yes r | _ = yes (here r)
... | no _  | yes s = yes (there s)
... | no r  | no s = no (λ{(here k) → r k; (there k) → s k})


data merge {a : Set} : (xs ys zs : List a) → Set where

  [] :
     ---------------
     merge [] [] []


  left-∷ : ∀ {x xs ys zs}
   → merge xs ys zs
     ----------------------------
   →  merge (x ∷ xs) ys (x ∷ zs)


  right-∷ : ∀ {y xs ys zs}
   → merge xs ys zs
     ----------------------------
   → merge xs (y ∷ ys) (y ∷ zs)

_ : merge [ 1 , 4 ] [ 2 , 3 ] [ 1 , 2 , 3 , 4 ]
_ = left-∷ (right-∷ (right-∷ (left-∷ [])))

-- merge is not functional
_ : merge [ 1 , 4 ] [ 2 , 3 ] [ 2 , 1 , 4 , 3 ]
_ = right-∷ (left-∷ (left-∷ (right-∷ [])))


split : ∀ {a : Set} {p : a → Set} (q : Decidable p) (zs : List a) →
  ∃[ xs ] ∃[ ys ] (merge xs ys zs × All p xs × All (¬_ ∘ p) ys)
split q [] = ⟨ [] , ⟨ [] , ⟨ [] , ⟨ [] , [] ⟩ ⟩ ⟩ ⟩
split q (x ∷ zs) with q x | split q zs
... | yes r | ⟨ xs , ⟨ ys , ⟨ mer , ⟨ fst , snd ⟩ ⟩ ⟩ ⟩ =
  ⟨ x ∷ xs , ⟨ ys , ⟨ left-∷ mer , ⟨ r ∷ fst , snd ⟩ ⟩ ⟩ ⟩
... | no r | ⟨ xs , ⟨ ys , ⟨ mer , ⟨ fst , snd ⟩ ⟩ ⟩ ⟩ =
  ⟨ xs , ⟨ x ∷ ys , ⟨ right-∷ mer , ⟨ fst , r ∷ snd ⟩ ⟩ ⟩ ⟩

