{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

--type Pairing f g = forall a b. f (a -> b) -> g a -> b

import Control.Comonad

import Data.Functor.Identity

import Stream

class Pairing f g | f -> g, g -> f where
    pair :: (a -> b -> c) -> f a -> g b -> c

instance Pairing Identity Identity where
    pair f (Identity a) (Identity b) = f a b

instance Pairing ((->) a) ((,) a) where
    pair f g (a,b) = f (g a) b 

uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry = pair ($)

move :: (Comonad w, Pairing m w) => w a -> m b -> w a
move space movement = pair (const id) movement (duplicate space)

s0 :: Stream Integer
s0 = naturals

data Sequence a = End a | Next (Sequence a)

instance Functor Sequence where
    fmap f (End x)   = End (f x)
    fmap f (Next xs) = Next (fmap f xs)  

-- This definition is consistent with 'ap', see coq file
instance Applicative Sequence where
    pure  = End
    (<*>) (End f)   (End a)   = End (f a)
    (<*>) (End f)   (Next as) = Next (fmap f as)
    (<*>) (Next fs) x         = Next (fs <*> x)

instance Monad Sequence where
    return  = End
    (>>=) (End a)   f   = f a
    (>>=) (Next as) f   = Next (as >>= f)

ap :: (Monad m) => m (a -> b) -> m a -> m b
ap mf ma = mf >>= \f -> ma >>= \a -> return (f a)

instance Pairing Sequence Stream where
    pair f (End a) (Cons b _) = f a b
    pair f (Next as) (Cons _ bs) = pair f as bs

s1 :: Stream Integer
s1 = move s0 (Next (End ()))

s2 :: Stream Integer
s2 = move s0 (Next (Next (End ())))