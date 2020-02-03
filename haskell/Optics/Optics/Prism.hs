{-# LANGUAGE RankNTypes                 #-}

module  Optics.Prism
    (   PrismC    (..)
    ,   PrismP
    ,   prismC2P
    ,   prismP2C
    )   where

import Data.Profunctor

import Optics.Optic
import Optics.Profunctor

data  PrismC a b s t
    = PrismC 
    { match :: s -> Either t a
    , build :: b -> t 
    }

type PrismP a b s t = forall p . Cocartesian p => Optic p a b s t


instance Profunctor (PrismC a b) where
    dimap f g (PrismC m b) = PrismC ((plus g id) . m . f) (g . b)


instance Cocartesian (PrismC a b) where
    left (PrismC m b) = PrismC
        (either ((plus Left id) . m) (Left . Right))
        (Left . b)
    right (PrismC m b) = PrismC
        (either (Left . Left) ((plus Right id) . m))
        (Right . b)

prismC2P :: PrismC a b s t -> PrismP a b s t
prismC2P (PrismC m b) = dimap m (either id b) . right


prismP2C :: PrismP a b s t -> PrismC a b s t
prismP2C f = f (PrismC Right id)


