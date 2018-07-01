{-# LANGUAGE RankNTypes #-}

data Free f a = Pure a | Free (f (Free f a))

instance Functor f => Functor (Free f) where
    fmap g (Pure a) = Pure (g a)
    fmap g (Free k) = Free (fmap (fmap g) k)

instance Functor f => Applicative (Free f) where
    pure                  = Pure
    <*> (Pure g) (Pure a) = Pure (g a)
    <*> (Free k) (Pure a) = ...



