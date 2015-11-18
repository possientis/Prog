-- Set already defined somwehere, just fooling around
data Set a = A [a] deriving (Show)

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

