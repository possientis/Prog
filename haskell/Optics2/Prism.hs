{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE RecordWildCards        #-}

module Prism
  ( ClonePrism
  , Prism
  , Prism'
  , clonePrism
  , isoToPrism
  , prism
  ) where

import Choice
import Iso
import PrismWitness
import Profunctor


type Prism s t a b = forall p . (Choice p) => p a b -> p s t
type Prism' s a = Prism s s a a

prism :: (s -> Either t a) -> (b -> t) -> Prism s t a b
prism match build pab = dimap before after pab' -- :: p s t
  where
    pab'      = right pab                       -- :: p (Either t a) (Either t b) 
    before    = match                           -- :: s -> Either t a
    after     = either id build                 -- :: Either t b -> t

isoToPrism :: Iso s t a b -> Prism s t a b
isoToPrism i = i

class ClonePrism w s t a b | w -> s t a b where
  clonePrism :: w -> Prism s t a b

instance ClonePrism (PrismWitness a b s t) s t a b where
  clonePrism PrismWitness {..} = prism match build 

_fromWitness :: PrismWitness a b s t -> Prism s t a b
_fromWitness = clonePrism

_toWitness :: Prism s t a b -> PrismWitness a b s t
_toWitness p = p prismId

