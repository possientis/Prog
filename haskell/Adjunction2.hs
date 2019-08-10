{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeSynonymInstances   #-}

class (Functor l, Functor r) => Adjunction l r where
    to   :: (l a -> c) -> (a -> r c)
    from :: (a -> r c) -> (l a -> c)


newtype L b a = L (a,b) 

newtype R b c =  R (b -> c)

instance Functor (L b) where
    fmap f (L (a,b)) = L (f a, b)

instance Functor (R b) where
    fmap f (R g) = R (f . g)

instance Adjunction (L b) (R b) where
    to f a = R (\y -> f (L (a, y)))
    from f (L (a,b)) = g b where (R g) = f a 
 
to' :: ([a] -> m) -> a -> m
to' f x = f [x]

from' :: (Monoid m) => (a -> m) -> [a] -> m
from' f = mconcat . map f


