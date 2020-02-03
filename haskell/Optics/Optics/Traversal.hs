{-# LANGUAGE RankNTypes                 #-}

module  Optics.Traversal
    (   TraversalC   (..)
    ,   TraversalP
    )   where

import Optics.Optic
import Optics.FunList
import Optics.Profunctor


-- FunList a b t ~ a^n x (b^n -> t)

data TraversalC a b s t = TraversalC { extract :: s -> FunList a b t }


type TraversalP a b s t 
    = forall p . (Cartesian p, Cocartesian p, Monoidal p) => Optic p a b s t 
    
