{-# LANGUAGE RankNTypes                 #-}

module  Optics.Lens
    (   LensC    (..)
    ,   LensP
    )   where

import Data.Profunctor

import Optics.Optic
import Optics.Profunctor

data  LensC a b s t 
    = LensC 
    { view :: s -> a
    , update :: (b,s) -> t 
    }

type LensP a b s t = forall p . Cartesian p => Optic p a b s t


instance Profunctor (LensC a b) where
    dimap f g (LensC v u) = LensC (v . f) (g . u . (cross id f))

instance Cartesian (LensC a b) where
    first (LensC v u) = LensC (v . fst) (fork (u . cross id fst) (snd . snd)) 
    second = undefined 

fork :: (a -> b) -> (a -> c) -> a -> (b,c)
fork f g x = (f x, g x)



