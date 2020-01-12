{-# LANGUAGE RankNTypes         #-}

module  Optics.Try
    (
    )   where

import Data.Profunctor

type Optic p a b s t = p a b -> p s t

data IsoC a b s t = IsoC { o :: s -> a , i :: b -> t }

type IsoP a b s t = forall p . Profunctor p => Optic p a b s t

isoC2P :: IsoC a b s t -> IsoP a b s t
isoC2P (IsoC o i) = dimap o i

instance Profunctor (IsoC a b) where
    dimap l r (IsoC o i) = IsoC (o . l) (r . i)

isoP2C :: IsoP a b s t -> IsoC a b s t 
isoP2C f = f (IsoC id id)


isoP2P :: IsoP a b s t -> IsoP a b s t
isoP2P f = isoC2P (isoP2C f)

isoC2C :: IsoC a b s t -> IsoC a b s t
isoC2C x = isoP2C (isoC2P x)

