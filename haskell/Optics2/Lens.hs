{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE RecordWildCards        #-}

module Lens
  ( CloneLens
  , Lens
  , Lens'
  , cloneLens
  , isoToLens
  , lens
  ) where

import Iso
import LensWitness
import Profunctor
import Strong

-- Def: Given s t a b, we call 'lens' (w.r. to s t a b) a value of the type Lens s t a b
-- defined below. A lens is therefore essentially a polymorphic function which maps
-- any transformation of type a ~> b to a transformation of type s ~> t, across
-- all strong profunctors.
type Lens s t a b = forall p . (Strong p) => p a b -> p s t
type Lens' s a = Lens s s a a

-- It is possible to create a lens from a 'get' and a 'set'
lens :: (s -> a) -> (b -> s -> t) -> Lens s t a b
lens get set pab = dimap before after pab'  -- :: p s t   
  where
    pab'         = first pab                -- :: p (a, s) (b, s) 
    before s     = (get s, s)               -- :: (a ,s) 
    after (b, s) = set b s                  -- :: t 

-- It is possible to create a lens from an Iso
isoToLens :: Iso s t a b -> Lens s t a b
isoToLens i = i

-- Def: we say that a type w is 'lens clonable' (w.r. to s t a b) if there
-- exists a cloning map between its elements and Lens s t a b. 
class CloneLens w s t a b | w -> s t a b where
  cloneLens :: w -> Lens s t a b

-- Lemma: For all s t a b, LensWitness a b s t is lens clonable.
instance CloneLens (LensWitness a b s t) s t a b where
  cloneLens LensWitness {..} = lens get set 

_fromWitness :: LensWitness a b s t -> Lens s t a b
_fromWitness = cloneLens

_toWitness :: Lens s t a b -> LensWitness a b s t
_toWitness l = l lensId

