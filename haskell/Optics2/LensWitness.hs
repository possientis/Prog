{-# LANGUAGE TupleSections  #-}

module LensWitness
  ( LensWitness (..)
  , lensId
  ) where

import Data.Tuple.Extra ((***))
import Profunctor
import Strong

-- This definition is important and is motivated below
newtype LensWitness a b s t = LensWitness { unLensWitness :: s -> (a, b -> t) }

-- Remark: given types a, b, LemsWitness a b is a binary type constructor, and
-- values of type LensWitness a b s t are transformations from s to t, i.e. some 
-- value of type s ~> t. The exact nature of this transformation may not be
-- very clear. However, given a transformation g : s ~> t and value x :: s, we can 
-- derive a value y :: a and a function f :: b -> t. If we had some function 
-- of type a -> b, we would be able to derive a value of type t from x :: s. So
-- the transformation g :: s ~> t may be heuristically viewed at some sort of
-- function from s to t 'with a hole', i.e. where the step from a to b is missing.
--
-- Remark: we can easily see that given a b and a transformation g :: s ~> t
-- (relative to LensWitness a b), given functions f :: s' -> s and h :: t -> t',
-- we can create a transformation of type s' ~> t'. In other words:

-- Lemma: For all a b, LemsWitness a b is a Profunctor.
instance Profunctor (LensWitness a b) where
  dimap f h g = LensWitness $ (id *** (h .)) . unLensWitness g . f

-- Lemma: For all a b, LensWitness a b is Strong
instance Strong (LensWitness a b) where
  first g =  LensWitness $ k . (unLensWitness g *** id)
    where
      k ((a,f),c) = (a, (,c) . f)

-- Not that LensWitness a b a b has an obvious element:
lensId :: LensWitness a b a b
lensId = LensWitness (,id)
