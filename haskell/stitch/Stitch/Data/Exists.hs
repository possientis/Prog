{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE QuantifiedConstraints  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TypeInType             #-}

module Stitch.Data.Exists
  ( Ex  (..)
  , packEx
  , unPackEx
  ) where

import Data.Kind

import Stitch.Data.Nat
import Stitch.Data.Vec

data Ex :: (k -> Type) -> Type  where
  Ex :: forall f i . f i -> Ex f

instance (forall i . Show (f i)) => Show (Ex f) where
  show (Ex x) = show x

packEx :: forall f i . f i -> Ex f
packEx = Ex

unPackEx :: Ex f -> (forall i . f i -> r) -> r
unPackEx (Ex x) k = k x

newtype Vec' a n = Vec' { _unVec' :: Vec n a }
  deriving Show

_test1 :: Ex (Vec' Int)
_test1 = packEx . Vec' $ (2 :> 1 :> 0 :> VNil)

_test2 :: Ex (Vec' Int)
_test2 = packEx . Vec' $ (3 :> 2 :> 1 :> 0 :> VNil)

_test3 :: Vec ('Succ ('Succ 'Zero)) (Ex (Vec' Int))
_test3 = _test1 :> _test2 :> VNil

_exVecSum :: Ex (Vec' Int) -> Int
_exVecSum (Ex (Vec' v)) = go v where
  go :: Vec n Int -> Int
  go VNil = 0
  go (x :> xs) = x + go xs


