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
    (d : a) → bst l' d → bst d u' → l ≤ l' → u' ≤ u → bst u l

bst-lookup : {l u : a} → a → bst l u → maybe a
bst-lookup d (bst-leaf x)            = nothing
bst-lookup d (bst-node d' tl tr _ _) with ≡-dec d d' 
bst-lookup d (bst-node d' tl tr _ _) | left  p = just d
bst-lookup d (bst-node d' tl tr _ _) | right p with ≤-dec d d' 
bst-lookup d (bst-node d' tl tr _ _) | right p | left  q = bst-lookup d tl
bst-lookup d (bst-node d' tl tr _ _) | right p | right q = bst-lookup d tr


bst-insert :{l u : a} → (d : a) → bst l u → bst (min d l) (max d u)
bst-insert {l} {u} d (bst-leaf p) with ≤-total d l
bst-insert {_} {_} d (bst-leaf p) | left  q =
  bst-node d (bst-leaf (≤-refl d)) (bst-leaf (≤-trans q p)) {!!} {!!}
bst-insert {_} {_} d (bst-leaf p) | right x = {!!}
bst-insert d (bst-node d₁ t t₁ x x₁) = {!!}






