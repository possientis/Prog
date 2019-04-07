module  Field
    (   Field (..)
    ,   (-)
    ,   (/)
    ,   pow
    )   where

import Prelude hiding   ((+),(-),(*),(/))

class (Eq a) => Field a where
    (+)    :: a -> a -> a
    (*)    :: a -> a -> a
    neg    :: a -> a
    inv    :: a -> a
    zero   :: a
    one    :: a 

(-) :: (Field a) => a -> a -> a
(-) x y = x + neg y

(/) :: (Field a) => a -> a -> a
(/) x y 
    | y == zero = error "Field division by zero"
    | otherwise = x * inv y

pow :: (Field a) => a -> Integer -> a 
pow x n
    | n == 0    = one
    | n < 0     = inv $ pow x (-n)
    | even n    =     pow (x * x) (n `div` 2)
    | odd  n    = x * pow (x * x) (n `div` 2) 
    | otherwise = error "pow: this error should never happen"

