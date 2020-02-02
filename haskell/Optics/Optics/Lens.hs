{-# LANGUAGE RankNTypes                 #-}

module  Optics.Lens
    (   LensC    (..)
    ,   LensP
    ,   lensC2P
    ,   lensP2C
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
    first  (LensC v u) = LensC (v . fst) (fork (u . cross id fst) (snd . snd)) 
    second (LensC v u) = LensC (v . snd) (fork (fst . snd) (u . cross id snd)) 

lensC2P :: LensC a b s t -> LensP a b s t
lensC2P (LensC v u) = dimap (fork v id) u . first

lensP2C :: LensP a b s t -> LensC a b s t
lensP2C f = f (LensC id fst)



