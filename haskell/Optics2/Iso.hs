{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}

module Iso
  ( CloneIso
  , Iso  (..)
  , cloneIso
  , iso
  ) where

import IsoWitness
import Optic
import Profunctor

newtype Iso s t a b = Iso { unIso :: forall p . (Profunctor p) => p a b -> p s t }

data Simple s t a b = Simple
  { _from :: s -> a
  , _to   :: b -> t
  } 

iso :: (s -> a) -> (b -> t) -> Iso s t a b
iso from to = Iso (dimap from to)

type AnIso s t a b = Optic (IsoWitness a b) s t a b

class CloneIso w s t a b | w -> s t a b where
  cloneIso :: w -> Iso s t a b

instance CloneIso (Iso s t a b) s t a b where
  cloneIso = id

instance CloneIso (Simple s t a b) s t a b where
  cloneIso (Simple from to) = iso from to

instance CloneIso (IsoWitness a b s t) s t a b where
  cloneIso iw = iso from to where
    from =  fst (unIsoWitness iw)
    to   =  snd (unIsoWitness iw)

instance CloneIso (AnIso s t a b) s t a b where
  cloneIso wab = cloneIso (wab isoId)

_fromSimple :: Simple s t a b -> Iso s t a b
_fromSimple = cloneIso

_toSimple :: Iso s t a b -> Simple s t a b
_toSimple i = Simple (fst f) (snd f) where
  f = unIsoWitness . unIso i $ isoId









