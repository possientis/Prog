{-# LANGUAGE RankNTypes                 #-}

module  Optics.Prism
    (   PrismC    (..)
    ,   PrismP
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
    left = undefined
    right = undefined


