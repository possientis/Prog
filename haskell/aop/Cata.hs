{-# LANGUAGE LambdaCase         #-}
module  Cata
    (   sum
    ,   length
    ,   average
    )   where

import Prelude  hiding (sum, length, div)
import Data.Functor.Foldable
import Data.Tuple.Extra

(+++) :: b -> (a -> b -> b) -> ListF a b -> b
(+++) b op = \case
    Nil       -> b
    Cons x y  -> op x y 

div :: (Fractional a) => (a,Int) -> a
div (a,n) = a / fromIntegral n

sum :: (Num a) => [a] -> a
sum = cata $  0 +++ (+)

length :: [a] -> Int
length = cata $ 0 +++ (\_ n -> n + 1)

average :: (Fractional a) => [a] -> a
average = div . (sum &&& length)

