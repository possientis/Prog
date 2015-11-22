-- Set already defined somwehere, just fooling around
data Set a = A [a] deriving (Show -- , Eq) we do not want 'equality as lists'
-- we want 'equality as sets', need to implement interface Eq (type class Eq)

element:: Eq a => a -> Set a -> Bool
element x (A xs) = elem x xs

nil :: Set a
nil = A []

insert :: a -> Set a -> Set a
insert x (A xs) = A (x:xs)

subset :: Eq a => Set a -> Set a -> Bool
subset (A xs) (A ys) = and [elem x ys | x <- xs]

equal :: Eq a => Set a -> Set a -> Bool
equal x y = subset x y && (subset y x)

-- nice use of zip
isOrdered :: Ord a => [a] -> Bool
isOrdered xs = and [x < y | (x,y) <- zip xs (tail xs)]

set1 = A [1,0,2,3]
set2 = A [0,1,2,3]

-- implementing == of Eq interface (type class)
-- 'instance' keyword

instance Eq a => Eq (Set a) where -- you need equality for type a
  s == t = (equal s t)

