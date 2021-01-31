module  Stream 
    (   Stream  (..)
    ,   naturals
    ,   toList
    ,   unfoldStream
    )   where 

import Control.Comonad


data Stream a = Cons a (Stream a)

from :: Integer -> Stream Integer
from n = Cons n (from (n + 1))

naturals :: Stream Integer
naturals = from 0

toList :: Integer -> Stream a -> [a]
toList n (Cons a s)
    | n <= 0 = []
    | otherwise = a : toList (n - 1) s

instance Functor Stream where
    fmap f (Cons a s) = Cons (f a) (fmap f s)

instance Comonad Stream where
    extract (Cons a _) = a
    duplicate s@(Cons _ s') = Cons s (duplicate s')

sumWithNext :: Num a => Stream a -> a
sumWithNext (Cons a (Cons a' _)) = a + a'

_stream0 :: Stream Integer
_stream0 = extend sumWithNext naturals

next :: Stream a -> a
next (Cons _ (Cons a _)) = a

_first3 :: Stream a -> [a]
_first3 stream = 
    let stream2 = stream  =>> next
        stream3 = stream2 =>> next
    in [extract stream, extract stream2, extract stream3]

unfoldStream :: s -> (s -> (a,s)) -> Stream a
unfoldStream initState getNext = Cons a (unfoldStream nextState getNext)
    where
    (a, nextState) = getNext initState


