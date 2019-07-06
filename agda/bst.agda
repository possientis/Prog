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
  bst-leaf  : ∀ {l u : a} → l ≤ u → bst l u
  bst-node  : ∀ {l u : a}
    (d : a) → bst l d → bst d u → bst l u
  bst-left  : ∀ {l l' u : a} → l ≤ l' → bst l' u  → bst l u  -- left cast
  bst-right : ∀ {l u u' : a} → u' ≤ u → bst l  u' → bst l u  -- right cast 

bst-lookup : {l u : a} → a → bst l u → maybe a
bst-lookup {l} {u} d (bst-leaf p)       = nothing
bst-lookup {l} {u} d (bst-node e tl tr) with ≡-dec d e 
bst-lookup {l} {u} d (bst-node e tl tr) | left  p = just d
bst-lookup {l} {u} d (bst-node e tl tr) | right p with ≤-dec d e 
bst-lookup {l} {u} d (bst-node e tl tr) | right p | left  q = bst-lookup d tl
bst-lookup {l} {u} d (bst-node e tl tr) | right p | right q = bst-lookup d tr
bst-lookup {l} {u} d (bst-left p t)     = bst-lookup d t
bst-lookup {l} {u} d (bst-right p t)    = bst-lookup d t

bst-order : ∀ {l u : a } → bst l u → l ≤ u
bst-order {l} {u} (bst-leaf p)       = p
bst-order {l} {u} (bst-node d tl tr) = ≤-trans (bst-order tl) (bst-order tr)
bst-order {l} {u} (bst-left p t)     = ≤-trans p (bst-order t)
bst-order {l} {u} (bst-right p t)    = ≤-trans (bst-order t) p


bst-insert :{l u : a} → (d : a) → bst l u → bst (min d l) (max d u)
bst-insert {l} {u} d (bst-leaf p) with ≤-total d l
bst-insert {l} {u} d (bst-leaf p) | left q  with ≤-total d u 
bst-insert {l} {u} d (bst-leaf p) | left q | left  r =
  bst-node d (bst-leaf (≤-refl d)) (bst-leaf r)
bst-insert {l} {u} d (bst-leaf p) | left q | right r =
  bst-node d (bst-leaf (≤-refl d)) (bst-leaf (≤-refl d)) 
bst-insert {l} {u} d (bst-leaf p) | right q with ≤-total d u 
bst-insert {l} {u} d (bst-leaf p) | right q | left  r =
  bst-node d (bst-leaf q) (bst-leaf r)
bst-insert {l} {u} d (bst-leaf p) | right q | right r =
  bst-node d (bst-leaf q) (bst-leaf (≤-refl d))
bst-insert {l} {u} d (bst-node e tl tr) with ≤-total d l  
bst-insert {l} {u} d (bst-node e tl tr) | left  p with ≤-total d u 
bst-insert {l} {u} d (bst-node e tl tr) | left p | left  q =
  bst-node e
    (bst-left (min-glb (≤-refl d) p)  
      (bst-right (max-lub (≤-trans p (bst-order tl)) (≤-refl e))
        (bst-insert d tl)))
    tr
bst-insert {l} {u} d (bst-node e tl tr) | left p | right q = {!!}
bst-insert {l} {u} d (bst-node e tl tr) | right p = {!!}
bst-insert {l} {u} d (bst-left p t)     = {!!}
bst-insert {l} {u} d (bst-right p t)    = {!!}





