open import id
open import sum
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
  bst-cast  : ∀ {l l' u u' : a} → l ≤ l' → u' ≤ u → bst l' u'  → bst l u


bst-lookup : {l u : a} → a → bst l u → maybe a
bst-lookup {l} {u} d (bst-leaf p)       = nothing
bst-lookup {l} {u} d (bst-node e tl tr) with ≡-dec d e 
bst-lookup {l} {u} d (bst-node e tl tr) | left  p = just d
bst-lookup {l} {u} d (bst-node e tl tr) | right p with ≤-dec d e 
bst-lookup {l} {u} d (bst-node e tl tr) | right p | left  q = bst-lookup d tl
bst-lookup {l} {u} d (bst-node e tl tr) | right p | right q = bst-lookup d tr
bst-lookup {l} {u} d (bst-cast p q t) = bst-lookup d t


bst-order : ∀ {l u : a } → bst l u → l ≤ u
bst-order {l} {u} (bst-leaf p)       = p
bst-order {l} {u} (bst-node d tl tr) = ≤-trans (bst-order tl) (bst-order tr)
bst-order {l} {u} (bst-cast p q t)   = ≤-trans p ( ≤-trans (bst-order t) q)


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
    (bst-cast
      (min-glb (≤-refl d) p)
      (max-lub (≤-trans p (bst-order tl)) (≤-refl e))
      (bst-insert d tl))
    tr
bst-insert {l} {u} d (bst-node e tl tr) | left p | right q =
  bst-node d
    (bst-cast p (≤-trans (bst-order tr) q) tl)
    (bst-cast (≤-trans p (bst-order tl)) q tr)
bst-insert {l} {u} d (bst-node e tl tr) | right p with ≤-total d u
bst-insert {l} {u} d (bst-node e tl tr) | right p | left  q  with ≤-total d e
bst-insert {l} {u} d (bst-node e tl tr) | right p | left q | left  r =
  bst-node e
    (bst-cast
      (min-glb p (≤-refl l))
      (max-lub r (≤-refl e))
      (bst-insert d tl))
    tr
bst-insert {l} {u} d (bst-node e tl tr) | right p | left q | right r =
  bst-node e
    tl
    (bst-cast
      (min-glb r (≤-refl e))
      (max-lub q (≤-refl u))
      (bst-insert d tr))
bst-insert {l} {u} d (bst-node e tl tr) | right p | right q =
  bst-node e tl (bst-node d (bst-cast (≤-refl e) q tr) (bst-leaf (≤-refl d)))
bst-insert {l} {u} d (bst-cast pl pu t) with ≤-total d l
bst-insert {l} {u} d (bst-cast pl pu t) | left  p with ≤-total d u 
bst-insert {l} {u} d (bst-cast pl pu t) | left p | left  q = 
  bst-cast
    (min-glb (≤-refl d) (≤-trans p pl))
    (max-lub q pu)
    (bst-insert d t)
bst-insert {l} {u} d (bst-cast pl pu t) | left p | right q = 
  bst-cast
    (min-glb (≤-refl d) (≤-trans p pl))
    (max-lub (≤-refl d) (≤-trans pu q))
    (bst-insert d t)
bst-insert {l} {u} d (bst-cast pl pu t) | right p with ≤-total d u 
bst-insert {l} {u} d (bst-cast pl pu t) | right p | left  q =
  bst-cast
    (min-glb p pl)
    (max-lub q pu)
    (bst-insert d t)
bst-insert {l} {u} d (bst-cast pl pu t) | right p | right q =
  bst-cast
    (min-glb p pl)
    (max-lub (≤-refl d) (≤-trans pu q))
    (bst-insert d t)




