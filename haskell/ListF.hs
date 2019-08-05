data List a = Nil | Cons a (List a)

from :: (Num a) => a -> List a
from x = Cons x $ from (x + 1)

all :: (Num a) => List a
all = from 0

data ListF a r = NilF | ConsF a r

instance Functor (ListF a) where
    fmap f NilF = NilF
    fmap f (ConsF x y) = ConsF x (f y) 

data Fix f = Fix { unFix :: f (Fix f) }

type List_ a = Fix (ListF a)

f :: List a -> List_ a 
f Nil         = Fix NilF
f (Cons x xs) = Fix (ConsF x (f xs)) 
    

g :: List_ a -> List a
g (Fix NilF)         = Nil
g (Fix (ConsF x xs)) = Cons x (g xs)


toList :: List a -> [a]
toList Nil         = []
toList (Cons x xs) = x : toList xs

fromList :: [a] -> List a
fromList []       = Nil
fromList (x : xs) = Cons x (fromList xs)

x :: [Int]
x = toList . g . f . fromList $ [1..20]

