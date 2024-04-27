{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE RecordWildCards        #-}

module Affine
  ( CloneAffine
  , Affine
  , Affine'
  , affine
  , cloneAffine
  , isoToAffine
  , lensToAffine
  , overA
  , prismToAffine
  , unAffineA
  ) where

import AffineWitness
import Choice
import Iso
import Lens
import Optic
import Prism
import Profunctor
import Strong


type Affine' s t a b = forall p . (Strong p, Choice p) => p a b -> p s t 
type Affine s a = Affine' s s a a

affine :: (s -> Either t (a, b -> t)) -> Affine' s t a b 
affine unAffine pab = dimap before after pab'   -- :: p s t
  where
    pab' = right . first $ pab -- :: p (Either t (a, b -> t)) (Either t (b, b -> t)) 
    before = unAffine                 -- s -> Either t (a, b -> t)
    after = either id $ \(b,g) -> g b -- Either t (b, b -> t) -> t

class CloneAffine w s t a b | w -> s t a b where
  cloneAffine :: w -> Affine' s t a b

instance CloneAffine (AffineWitness a b s t) s t a b where
  cloneAffine AffineWitness {..} = affine unAffine

_fromWitness :: AffineWitness  a b s t -> Affine' s t a b
_fromWitness = cloneAffine

_toWitness :: Affine' s t a b -> AffineWitness a b s t 
_toWitness a = a affineId

unAffineA :: Affine' s t a b -> s -> Either t (a, b -> t)
unAffineA a = unAffine . a $ affineId

overA :: Affine' s t a b -> (a -> b) -> (s -> t)
overA a = over a

lensToAffine :: Lens' s t a b -> Affine' s t a b
lensToAffine l = l

prismToAffine :: Prism' s t a b -> Affine' s t a b
prismToAffine p = p

isoToAffine :: Iso' s t a b -> Affine' s t a b
isoToAffine i = i
