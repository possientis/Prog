open import id
open import sum
open import relations

module min-max {ℓ ℓ'} {a : Set ℓ}
  (_≤_ : a -> a -> Set ℓ')
  (≤-reflexive : reflexive _≤_)
  (≤-antisymmetric : antisymmetric _≤_)
  (≤-total : total _≤_)
  where

min : a -> a -> a
min x y with ≤-total x y
min x y | left  p = x
min x y | right p = y

max : a -> a -> a
max x y with ≤-total x y
max x y | left  p = y
max x y | right p = x

min-x-y-≤-y : (x y : a) → min x y ≤ y
min-x-y-≤-y x y with ≤-total x y 
min-x-y-≤-y x y | left  p = p
min-x-y-≤-y x y | right p = ≤-reflexive y

y-≤-max-x-y :(x y : a) → y ≤ max x y
y-≤-max-x-y x y with ≤-total x y
y-≤-max-x-y x y | left  p = ≤-reflexive y
y-≤-max-x-y x y | right p = p


min-x-y-≤-x : (x y : a) → min x y ≤ x
min-x-y-≤-x x y with ≤-total x y 
min-x-y-≤-x x y | left  p = ≤-reflexive x
min-x-y-≤-x x y | right p = p

x-≤-max-x-y : (x y : a) → x ≤ max x y
x-≤-max-x-y x y with ≤-total x y
x-≤-max-x-y x y | left  p = p
x-≤-max-x-y x y | right p = ≤-reflexive x

min-glb : {x y z : a} → z ≤ x → z ≤ y → z ≤ min x y
min-glb {x} {y} {z} p q  with ≤-total x y 
min-glb {x} {y} {z} p q | left  r = p
min-glb {x} {y} {z} p q | right r = q

max-lub : {x y z : a} → x ≤ z → y ≤ z → max x y ≤ z
max-lub {x} {y} {z} p q with ≤-total x y
max-lub {x} {y} {z} p q | left  r = q
max-lub {x} {y} {z} p q | right r = p

min-comm : (x y : a) → min x y ≡ min y x
min-comm x y with ≤-total x y
min-comm x y | left  p with ≤-total y x 
min-comm x y | left p  | left  q =  ≤-antisymmetric p q
min-comm x y | left p  | right q = refl x
min-comm x y | right p with ≤-total y x
min-comm x y | right p | left  q = refl y
min-comm x y | right p | right q = ≤-antisymmetric p q

max-comm : (x y : a) → max x y ≡ max y x
max-comm x y with ≤-total x y
max-comm x y | left  p with ≤-total y x 
max-comm x y | left p  | left  q = ≤-antisymmetric q p
max-comm x y | left p  | right q = refl y
max-comm x y | right p with ≤-total y x
max-comm x y | right p | left  q = refl x
max-comm x y | right p | right q = ≤-antisymmetric q p




