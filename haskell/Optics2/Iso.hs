{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE RecordWildCards        #-}

module Iso
  ( CloneIso
  , Iso 
  , Iso'
  , cloneIso
  , iso
  ) where

import IsoWitness
import Profunctor

type Iso s t a b = forall p . (Profunctor p) => p a b -> p s t
type Iso' s a = Iso s s a a 

iso :: (s -> a) -> (b -> t) -> Iso s t a b
iso from to = dimap from to

class CloneIso w s t a b | w -> s t a b where
  cloneIso :: w -> Iso s t a b

instance CloneIso (IsoWitness a b s t) s t a b where
  cloneIso IsoWitness {..} = iso from to 

_fromWitness :: IsoWitness a b s t  -> Iso s t a b
_fromWitness = cloneIso

_toWitness :: Iso s t a b -> IsoWitness a b s t
_toWitness i = i isoId
