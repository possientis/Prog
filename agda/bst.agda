open import id
open import maybe
open import min-max
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

bst-insert :{l u : a} → (d : a) → bst l u → bst (min d l) (max d u)
bst-insert d t = ?




