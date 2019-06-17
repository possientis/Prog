open import id
open import maybe
open import relations


module bst {ℓ ℓ'} {a : Set ℓ}
  (_≤_ : a → a → Set ℓ')
  (≤-reflexive : reflexive _≤_)
  (≤-trans : transitive _≤_)
  (≤-total : total _≤_)
  (≤-decidable : decidable _≤_)
  (≡-decidable : eq_decidable a)
  where

open import Agda.Primitive

data bst : a → a → Set (ℓ ⊔ ℓ') where
  bst-leaf : ∀ {l u : a} → l ≤ u → bst l u
  bst-node : ∀ {l l' u u' : a}
    (d : a) → bst l' d → bst d u' → l ≤ l' → u' ≤ u → bst u l

bst-lookup : {l u : a} → a → bst l u → maybe a
bst-lookup d (bst-leaf x)            = nothing
bst-lookup d (bst-node d' tl tr _ _) with ≡-decidable d d' 
bst-lookup d (bst-node d' tl tr _ _) | left  p = just d
bst-lookup d (bst-node d' tl tr _ _) | right p with ≤-decidable d d' 
bst-lookup d (bst-node d' tl tr _ _) | right p | left  q = bst-lookup d tl
bst-lookup d (bst-node d' tl tr _ _) | right p | right q = bst-lookup d tr

min : a -> a -> a
min x y with ≤-total x y
min x y | left  p = x
min x y | right p = y

min-x-y-≤-y : (x y : a) → min x y ≤ y
min-x-y-≤-y x y with ≤-total x y 
min-x-y-≤-y x y | left  p = p
min-x-y-≤-y x y | right p = ≤-reflexive y


min-x-y-≤-x : (x y : a) → min x y ≤ x
min-x-y-≤-x x y with ≤-total x y 
min-x-y-≤-x x y | left  p = ≤-reflexive x
min-x-y-≤-x x y | right p = p

min-glb : (x y z : a) → z ≤ x → z ≤ y → z ≤ min x y
min-glb x y z p q  with ≤-total x y 
min-glb x y z p q | left  r = p
min-glb x y z p q | right r = q

min-comm : (x y : a) → min x y ≡ min y x
min-comm x y with ≤-total x y
min-comm x y | left  p = {!!}
min-comm x y | right p = {!!}




--bst-insert :{l u : a} → (d : a) → bst l u → bst (min d l) (max d u)



