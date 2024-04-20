{-# LANGUAGE RecordWildCards        #-}

module IsoWitness
  ( IsoWitness (..)
  , isoId
  ) where

import Profunctor


data IsoWitness a b s t = IsoWitness 
  { from :: s -> a
  , to   :: b -> t 
  }

isoId :: IsoWitness a b a b 
isoId  = IsoWitness 
  { from = id
  , to   = id
  }

-- Lemma :: For all a b, IsoWitness a b is a Profunctor
instance Profunctor (IsoWitness a b) where
  dimap f h IsoWitness {..} = IsoWitness
    { from = from . f
    , to   = h . to
    }
