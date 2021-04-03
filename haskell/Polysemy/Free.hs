{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE TypeOperators  #-}

module  Free
    (   Free        (..) 
    ,   (:->)
    ,   runFree
    )   where

import Control.Monad

type f :-> g = forall x . f x -> g x

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

runFree 
    :: (Monad m)
    => (f :-> m)
    -> Free f a
    -> m a
runFree _     (Pure k) = pure k
runFree alpha (Impure k) = alpha k >>= runFree alpha

