{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE ApplicativeDo  #-}

module  LensLike
    (   LensLike
    ,   Lens
    ,   Fold
    ,   Traversal
    ,   A   (..)
    ,   o1, o2 , o3, o4
    ,   values
    ,   ex1, ex2
    )   where

import Control.Lens hiding (Lens, Traversal, Fold, LensLike)
import Control.Applicative

data A = A { f1 :: Int , f2 :: String}

type LensLike f s t a b = (a -> f b) -> (s -> f t)

type Lens s t a b 
    = forall f . Functor f => LensLike f s t a b 

type Traversal s t a b 
    = forall f . Applicative f => LensLike f s t a b

type Fold s a 
    = forall f . (Contravariant f, Applicative f) => LensLike f s s a a

o1 :: Lens A A Int Int
o1 = undefined

o2 :: Traversal A A Int Int
o2 = o1 -- Every lens is a traversal

o3 :: Fold A Int
o3 = o1 -- Every lens is a fold

o4 :: Fold A Int
o4 = o2 -- Every traversal is a fold

-- values :: Traversal [a] [b] a b
values :: Applicative f => (a -> f b) -> [a] -> f [b]
-- values = traverse
values _ [] = pure []
values f (x : xs) = liftA2 (:) (f x) (values f xs)
{-
values f (x : xs) = do
    x  <- f x
    xs <- values f xs
    pure (x : xs)
-}
-- values f (x :xs) = (:) <$> f x <*> values f xs

ex1 :: [String]
ex1 = ["one", "two", "three"] ^.. values

ex2 :: [String]
ex2 = ["one", "two", "three"] & values %~ reverse
