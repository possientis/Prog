{-# LANGUAGE RecordWildCards  #-}

module PrismWitness
  ( PrismWitness  (..)
  , prismId
  ) where

import Profunctor
import Choice


data PrismWitness a b s t = PrismWitness 
  { match :: s -> Either t a 
  , build :: b -> t
  }

prismId :: PrismWitness a b a b
prismId  = PrismWitness 
  { match = Right 
  , build = id
  }

instance Profunctor (PrismWitness a b) where
  dimap f h PrismWitness {..} = PrismWitness
    { match = either (Left . h) Right . match . f 
    , build = h . build
    }

instance Choice (PrismWitness a b) where
  left PrismWitness {..} = PrismWitness
    { match = either (either (Left . Left) Right . match) (Left . Right)
    , build = Left . build
    }
