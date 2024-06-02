{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TupleSections    #-}

module AffineWitness
  ( AffineWitness (..)
  , AffineWitness' (..)
  , affineId'
  ) where

import Data.Bifunctor

import Profunctor
import Strong
import Choice

data AffineWitness a b s t = AffineWitness
  { match :: s -> Either t a
  , set   :: b -> s -> t
  }
 
newtype AffineWitness' a b s t = AffineWitness' { unAffine :: s -> Either t (a, b -> t) }

_fromWitness :: AffineWitness a b s t -> AffineWitness' a b s t
_fromWitness AffineWitness {..} = AffineWitness'
  { unAffine = \s -> case match s of
      Left t  -> Left t
      Right a -> Right (a, flip set s)
  }

_toWitness :: AffineWitness' a b s t -> AffineWitness a b s t
_toWitness AffineWitness' {..} = AffineWitness
  { match = \s -> case unAffine s of
      Left t     -> Left t
      Right (a,_) -> Right a
  , set = \b s -> case unAffine s of
      Left t  -> t
      Right u -> flip snd b u
  } 

toFrom :: AffineWitness a b s t -> AffineWitness a b s t
toFrom AffineWitness {..} =  AffineWitness
  { match = \s -> case match s of
      Left t -> Left t
      Right a -> Right a
  , set = \b s -> case match s of
      Left t -> t 
      Right a -> set b s
      
  }





affineId' :: AffineWitness' a b a b
affineId' = AffineWitness' { unAffine = Right . (,id) }

instance Profunctor (AffineWitness' a b) where
  dimap f h AffineWitness' {..} = AffineWitness'
    { unAffine =  bimap h g . unAffine . f }
    where
      g (a, k) = (a, h . k)

instance Strong (AffineWitness' a b) where
  first AffineWitness' {..} = AffineWitness'
    { unAffine = \(s,c) -> bimap (,c) (g c) . unAffine $ s
    }
    where
      g c (a, k) = (a, (,c) . k)

instance Choice (AffineWitness' a b) where
  left AffineWitness' {..} = AffineWitness'
    { unAffine = \sc -> case sc of
        Left s ->  case unAffine s of
          Left t       -> Left (Left t)
          Right (a, g) -> Right (a, Left . g)
        Right c -> Left (Right c)
    } 
