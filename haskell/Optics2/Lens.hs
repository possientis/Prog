{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}

module Lens
  ( CloneLens
  , Lens
  , Lens'
  , cloneLens
  , fromIso
  , lens
  ) where

import Iso
import LensWitness
import Optic
import Profunctor
import Strong

-- Def: Given s t a b, we call 'lens' (w.r. to s t a b) a value of the type Lens s t a b
-- defined below. A lens is therefore essentially a polymorphic function which maps
-- any transformation of type a ~> b to a transformation of type s ~> t, across
-- all strong profunctors.
type Lens s t a b = forall p . (Strong p) => p a b -> p s t
type Lens' s a = Lens s s a a

-- Consider a simple record type with a getter and a setter:
data Simple s t a b = Simple
  { _get :: s -> a
  , _set :: b -> s -> t 
  }

-- It is possible to create a lens from a 'get' and a 'set'
lens :: (s -> a) -> (b -> s -> t) -> Lens s t a b
lens get set pab = dimap before after pab'  -- :: p s t   
  where
    pab'         = first pab                -- :: p (a, s) (b, s) 
    before s     = (get s, s)               -- :: (a ,s) 
    after (b, s) = set b s                  -- :: t 

fromIso :: Iso s t a b -> Lens s t a b
fromIso i = i

-- Consider the type of optics relative to the Strong Profunctor LensWitness a b:
type ALens s t a b = Optic (LensWitness a b) s t a b 

-- Def: we say that a type w is 'lens clonable' (w.r. to s t a b) if there
-- exists a cloning map between its elements and Lens s t a b. 
class CloneLens w s t a b | w -> s t a b where
  cloneLens :: w -> Lens s t a b

-- Lemma: For all s t a b, Simple s t a b is lens clonable.
instance CloneLens (Simple s t a b) s t a b where
  cloneLens (Simple get set) = lens get set

-- The type LensWitness a b s t is clearly isomorphic to Simple s t a b, hence:
-- Lemma: For all s t a b, LensWitness a b s t is lens clonable.
instance CloneLens (LensWitness a b s t) s t a b where
  cloneLens lw = lens get set where
    get s   =  fst (unLensWitness lw s)
    set b s =  snd (unLensWitness lw s) b

-- A value of type ALens s t a b is simply a map from the type LensWitness a b a b 
-- to the type LensWitness a b s t. Hence, since LensWitness a b a b has an obvious
-- element, such a value gives us an element of LensWitness a b s t. Hence:
-- Lemma: For all s t a b, ALens s t a b is lens clonable.
instance CloneLens (ALens s t a b) s t a b where
  cloneLens wab = cloneLens (wab lensId)

-- So we know that a Simple lens gives rise to a (profucntor) lens:
_fromSimple :: Simple s t a b -> Lens s t a b
_fromSimple = cloneLens 

-- Conversely, a (profunctor lens) gives rise to a simple lens:
_toSimple :: Lens s t a b -> Simple s t a b
_toSimple l = Simple (fst . f) (flip $ snd . f)  where
  f = unLensWitness . l $ lensId

-- Remark: the fact that these two mappings should be inverse of
-- each other is far from obvious.
