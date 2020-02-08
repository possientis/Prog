{-# LANGUAGE RankNTypes                 #-}

module  Optics.Traversal
    (   TraversalC   (..)
    ,   TraversalP
    ,   traverse
    ,   out
    ,   inn
    )   where

import Prelude              hiding (traverse)
import Data.Profunctor

import Optics.Optic
import Optics.FunList
import Optics.Profunctor


-- FunList a b t ~ a^n x (b^n -> t)

data TraversalC a b s t 
    = TraversalC 
    { extract :: s -> FunList a b t 
    }


type TraversalP a b s t 
    = forall p . (Cartesian p, Cocartesian p, Monoidal p) => Optic p a b s t 
   
out :: FunList a b t -> Either t (a, FunList a b (b -> t))
out (Done t) = Left t
out (More a k) = Right (a,k)

inn :: Either t (a, FunList a b (b -> t)) -> FunList a b t
inn (Left t) = Done t
inn (Right (a,k)) = More a k

traverse 
    :: (Cocartesian p, Monoidal p) 
    => p a b
    -> p (FunList a c t) (FunList b c t)
traverse k = dimap out inn (right (par k (traverse k)))

instance Profunctor (TraversalC a b) where
    dimap f g (TraversalC e) = TraversalC $ unUpStar $ dimap f g (UpStar e)
