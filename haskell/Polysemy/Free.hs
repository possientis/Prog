module  Free
    (   Free        (..) 
    )   where

import Control.Monad

data Free f k
    = Pure k
    | Impure (f (Free f k)) 

instance Functor f => Functor (Free f) where
    fmap g (Pure a)    = Pure   $ g a
    fmap g (Impure fa) = Impure $ fmap (fmap g) fa

instance Functor f => Applicative (Free f) where
    pure  = return 
    (<*>) = ap

instance Functor f => Monad (Free f) where
    return = Pure
    (>>=) (Pure k) g = g k
    (>>=) (Impure k) g = Impure $ fmap (flip (>>=) g) k
