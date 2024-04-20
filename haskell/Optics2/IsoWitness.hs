{-# LANGUAGE TupleSections  #-}

module IsoWitness
  ( IsoWitness (..)
  , isoId
  ) where

import Profunctor


newtype IsoWitness a b s t = IsoWitness { unIsoWitness :: (s -> a, b -> t) }

isoId :: IsoWitness a b a b 
isoId  = IsoWitness (id,id)

-- Lemma :: For all a b, IsoWitness a b i sa Profunctor
instance Profunctor (IsoWitness a b) where
  dimap f h (IsoWitness g) = IsoWitness (fst g . f, h . snd g)
