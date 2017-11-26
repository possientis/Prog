{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances  #-}

import Control.Monad

data Free f a
    =  Pure a
    |  Free (f (Free f a))

-- standard Functor implementation from Applicative
instance (Functor f) => Functor (Free f) where
    fmap = (<*>) . pure

-- standard Applicative implementation from Monad
instance (Functor f) => Applicative (Free f) where
    pure  = return
    (<*>) = ap  -- need Control.Monad


instance (Functor f) => Monad (Free f) where
    return a        = Pure a
    Pure a >>= g    = g a 
    Free f >>= g    = Free (fmap (>>= g) f)


class Monad m => MonadFree f m where
    wrap :: f (m a) -> m a



instance (Functor f) => MonadFree f (Free f) where
    wrap = Free


liftF :: (Functor f, MonadFree f m) => f a -> m a
liftF = wrap . fmap return 

iter :: Functor f => (f a -> a) -> Free f a -> a
iter _ (Pure a) = a
iter phi (Free m) = phi (iter phi <$> m)


retract :: Monad f => Free f a -> f a
retract (Pure a)    = return a
retract (Free as)   = as >>= retract  



