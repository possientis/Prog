{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE QuantifiedConstraints  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TypeInType             #-}

module Stitch.Data.Exists
  ( Ex      (..)
  , SingEx  (..)
  , mapEx
  , packEx
  , packSingIEx
  , unpackEx
  , unpackSingIEx
  , test1
  ) where

import Data.Kind

import Stitch.Data.Nat
import Stitch.Data.Singletons
import Stitch.Data.Vec

data Ex :: (k -> Type) -> Type  where
  Ex :: forall f i . f i -> Ex f

instance (forall i . Show (f i)) => Show (Ex f) where
  show (Ex x) = show x

-- | Pack an existential
packEx :: forall f i . f i -> Ex f
packEx = Ex

-- | Unpack an existential (CPS-style)
unpackEx :: Ex f -> (forall i . f i -> r) -> r
unpackEx (Ex x) k = k x

-- | Map a function over the packed existential
mapEx :: (forall i . a i -> b i) -> Ex a -> Ex b
mapEx f (Ex x) = Ex (f x)

-- | Like 'Ex', but stores an implicit singleton describing the
-- existentially bound index
data SingEx :: (k -> Type) -> Type where
  SingEx :: SingI i => a i -> SingEx a

-- | Pack an existential with an implicit singleton
packSingIEx :: SingI i => a i -> SingEx a
packSingIEx = SingEx

-- | Unpack an existential with an implicit singleton (CPS-style)
unpackSingIEx :: SingEx a -> (forall i. SingI i => a i -> r) -> r
unpackSingIEx (SingEx x) k = k x

newtype Vec' a n = Vec' { _unVec' :: Vec n a }
  deriving Show

test1 :: Ex (Vec' Int)
test1 = packEx . Vec' $ (2 :> 1 :> 0 :> VNil)

_test2 :: Ex (Vec' Int)
_test2 = packEx . Vec' $ (3 :> 2 :> 1 :> 0 :> VNil)

_test3 :: Vec ('Succ ('Succ 'Zero)) (Ex (Vec' Int))
_test3 = test1 :> _test2 :> VNil

_exVecSum :: Ex (Vec' Int) -> Int
_exVecSum (Ex (Vec' v)) = go v where
  go :: Vec n Int -> Int
  go VNil = 0
  go (x :> xs) = x + go xs


