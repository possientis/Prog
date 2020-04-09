{-# LANGUAGE RankNTypes     #-}

module  LensLike
    (   LensLike
    ,   Lens
    ,   Traversal
    ,   A   (..)
    )   where

data A = A { f1 :: Int , f2 :: String}

type LensLike f s t a b = (a -> f b) -> (s -> f t)

type Lens s t a b 
    = forall f . Functor f => LensLike f s t a b 

type Traversal s t a b 
    = forall f . Applicative f => LensLike f s t a b

f1L :: Lens A A Int Int
f1L k s = undefined





