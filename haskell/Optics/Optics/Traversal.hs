{-# LANGUAGE RankNTypes                 #-}

module  Optics.Traversal
    (   TraversalC   (..)
    ,   TraversalP
    ,   traverse
    ,   traverseOf
    ,   traversalC2P
    ,   traversalP2C
    ,   out
    ,   inn
    )   where

import Prelude              hiding (traverse)
import Data.Profunctor

import Optics.Optic
import Optics.FunList
import Optics.Profunctor


-- FunList a b t ~ a^n x (b^n -> t)

-- Essentially the type UpStar F s t with functor F = FunList a b
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

instance Cartesian (TraversalC a b) where
    first  (TraversalC e) = TraversalC $ unUpStar $ first  (UpStar e)
    second (TraversalC e) = TraversalC $ unUpStar $ second (UpStar e)

instance Cocartesian (TraversalC a b) where
    left  (TraversalC e) = TraversalC $ unUpStar $ left  (UpStar e)
    right (TraversalC e) = TraversalC $ unUpStar $ right (UpStar e)

instance Monoidal (TraversalC a b) where
    par (TraversalC e1) (TraversalC e2) 
        = TraversalC 
        . unUpStar 
        $ par (UpStar e1) (UpStar e2)
    empty = TraversalC $ unUpStar $ empty


traversalC2P :: TraversalC a b s t -> TraversalP a b s t
traversalC2P (TraversalC e) k = dimap e fuse (traverse k)

traversalP2C :: TraversalP a b s t -> TraversalC a b s t
traversalP2C f = f (TraversalC single) 

traverseOf :: TraversalP a b s t -> (forall f . (Applicative f) => (a -> f b) -> s -> f t)
traverseOf p f = unUpStar $ p (UpStar f)

