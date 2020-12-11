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

stream :: Stream Integer
stream = extend sumWithNext naturals
