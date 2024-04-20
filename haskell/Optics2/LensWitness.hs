{-# LANGUAGE RecordWildCards  #-}

module LensWitness
  ( LensWitness (..)
  , lensId
  ) where

import Data.Tuple.Extra ((***))
import Profunctor
import Strong


data LensWitness a b s t = LensWitness
  { get :: s -> a
  , set :: b -> s -> t
  }

lensId :: LensWitness a b a b
lensId  = LensWitness
  { get = id
  , set = const
  }

-- Remark: given types a, b, LemsWitness a b is a binary type constructor, and
-- values of type LensWitness a b s t can therefore be viewed as transformations 
-- from s to t, i.e. as some value of type s ~> t. The exact nature of this 
-- transformation may not be very clear. However, given a transformation g : s ~> t 
-- and given a value x :: s, we can derive a value y :: a and also a function
-- f :: b -> t. If we had some function of type a -> b, we would be able to derive 
-- a value of type t from x :: s. So the transformation g :: s ~> t may be heuristically
-- viewed at some sort of function from s to t 'with a hole', i.e. where the step from a 
-- to b is missing.
--
-- Remark: we can easily see that given a b and a transformation g :: s ~> t
-- (relative to LensWitness a b), given functions f :: s' -> s and h :: t -> t',
-- we can create a transformation of type s' ~> t'. In other words:

-- Lemma: For all a b, LensWitness a b is a Profunctor.
instance Profunctor (LensWitness a b) where
  dimap f h LensWitness {..} = LensWitness
    { get = get . f
    , set = \b -> h . set b . f
    }

-- Lemma: For all a b, LensWitness a b is Strong
instance Strong (LensWitness a b) where
  first LensWitness {..} = LensWitness
    { get = get . fst
    , set = \b -> set b *** id
    }  
