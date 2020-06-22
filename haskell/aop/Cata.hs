{-# LANGUAGE LambdaCase         #-}
module  Cata
    (   sum
    ,   length
    ,   average
    ,   average2
    )   where

import Prelude  hiding (sum, length, div)
import Data.Functor.Foldable
import Data.Tuple.Extra

(+++) :: b -> (a -> b -> b) -> ListF a b -> b
(+++) b op = \case
    Nil       -> b
    Cons x y  -> op x y 

div :: (Eq a, Fractional a) => (a,Int) -> a
div (_,0) = 0   -- avoiding singularity
div (a,n) = a / fromIntegral n

sum :: (Num a) => [a] -> a
sum = cata $  0 +++ (+)

length :: [a] -> Int
length = cata $ 0 +++ const (+1)

-- This implementation of average using two catamorphisms with
-- base functor ListF effectively traverses the structure twice.
average :: (Eq a, Fractional a) => [a] -> a
average = div . (sum &&& length)

-- (cata &&& cata) can be expressed as a single catamorphism.
average2 :: (Eq a, Fractional a) => [a] -> a
average2 = div . (cata $ (0,0) +++ \x (s,n) -> (x + s, n + 1))

