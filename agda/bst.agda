open import id
open import relations

module bst {ℓ ℓ'} {a : Set ℓ}
  (_≤_ : a → a → Set ℓ')
  (≤-refl  : reflexive _≤_)
  (≤-anti  : antisymmetric _≤_)
  (≤-trans : transitive _≤_)
  (≤-total : total _≤_)
  (≤-dec   : decidable _≤_)
  (≡-dec   : eq_decidable a)
  where

open import Agda.Primitive

open import maybe
open import min-max _≤_ ≤-refl ≤-anti ≤-total

data bst : a → a → Set (ℓ ⊔ ℓ') where
  bst-leaf : ∀ {l u : a} → l ≤ u → bst l u
  bst-node : ∀ {l l' u u' : a}
    (d : a) → bst l' d → bst d u' → l ≤ l' → u' ≤ u → bst l u

bst-lookup : {l u : a} → a → bst l u → maybe a
bst-lookup d (bst-leaf x)            = nothing
bst-lookup d (bst-node d' tl tr _ _) with ≡-dec d d' 
bst-lookup d (bst-node d' tl tr _ _) | left  p = just d
bst-lookup d (bst-node d' tl tr _ _) | right p with ≤-dec d d' 
bst-lookup d (bst-node d' tl tr _ _) | right p | left  q = bst-lookup d tl
bst-lookup d (bst-node d' tl tr _ _) | right p | right q = bst-lookup d tr


bst-insert :{l u : a} → (d : a) → bst l u → bst (min d l) (max d u)
bst-insert {l} {u} d (bst-leaf p) with ≤-total d l
bst-insert {l} {u} d (bst-leaf p) | left  q with ≤-total d u
bst-insert {_} {u} d (bst-leaf p) | left  q | left r  =
  bst-node d (bst-leaf (≤-refl d)) (bst-leaf r) (≤-refl d) (≤-refl u)
bst-insert {_} {_} d (bst-leaf p) | left  q | right r =
  bst-node d (bst-leaf (≤-refl d)) (bst-leaf (≤-refl d)) (≤-refl d) (≤-refl d)
bst-insert {_} {u} d (bst-leaf p) | right q with ≤-total d u
bst-insert {l} {u} d (bst-leaf p) | right q | left  r =
  bst-node d (bst-leaf q) (bst-leaf r) (≤-refl l) (≤-refl u)
bst-insert {l} {_} d (bst-leaf p) | right q | right r =
  bst-node d (bst-leaf q) (bst-leaf (≤-refl d)) (≤-refl l) (≤-refl d)
bst-insert {l} {u} d (bst-node e tl tr p q) with ≤-total d l
bst-insert {l} {u} d (bst-node e tl tr pl pr) | left p  with ≤-total d u
bst-insert {l} {u} d (bst-node e tl tr pl pr) | left p | left  q =
  bst-node e {!!} tr {!!} pr
bst-insert {l} {u} d (bst-node e tl tr pl pr) | left p | right q = {!!}
bst-insert {l} {u} d (bst-node e tl tr pl pr) | right p = {!!}






