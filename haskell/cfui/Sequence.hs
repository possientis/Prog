module  Sequence
    (   Sequence    (..)
    )   where

import Control.Monad

data Sequence a = End a | Next (Sequence a)

instance Functor Sequence where
    fmap f (End x)   = End (f x)
    fmap f (Next xs) = Next (fmap f xs)  

instance Applicative Sequence where
    pure  = return
    (<*>) = ap

instance Monad Sequence where
    return  = End
    (>>=) (End a)   f   = f a
    (>>=) (Next as) f   = Next (as >>= f)


