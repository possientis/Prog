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
  , unpackSingEx
  , unpackSingIEx
  , test1
  ) where

import Data.Kind

import Stitch.Data.Nat
import Stitch.Data.Singletons
import Stitch.Data.Vec

data Ex :: forall k . (k -> Type) -> Type  where
  Ex :: forall k (f :: k -> Type)  (i :: k) . f i -> Ex f

instance (forall i . Show (f i)) => Show (Ex f) where
  show (Ex x) = show x

-- | Pack an existential
packEx :: forall k (f :: k -> Type) (i :: k) . f i -> Ex f
packEx = Ex

-- | Unpack an existential (CPS-style)
unpackEx 
  :: forall k (f :: k -> Type) (r :: Type) 
   . Ex f 
  -> (forall (i :: k) . f i -> r) 
  -> r
unpackEx (Ex x) k = k x

-- | Map a function over the packed existential
mapEx 
  :: forall k (a :: k -> Type) (b :: k -> Type) 
   . (forall (i :: k) . a i -> b i) 
  -> Ex a 
  -> Ex b
mapEx f (Ex x) = Ex (f x)

-- | Like 'Ex', but stores an implicit singleton describing the
-- existentially bound index
data SingEx :: forall k . (k -> Type) -> Type where
  SingEx 
    :: forall k (a :: k -> Type) (i :: k) 
     . SingI i 
    => a i 
    -> SingEx a

-- | Pack an existential with an implicit singleton
packSingIEx 
  :: forall k (a :: k -> Type) (i :: k) 
   . SingI i 
  => a i 
  -> SingEx a
packSingIEx = SingEx

-- | Unpack an existential with an implicit singleton (CPS-style)
unpackSingIEx 
  :: forall k (a :: k -> Type) (r :: Type) 
   . SingEx a 
  -> (forall (i :: k) . SingI i => a i -> r) 
  -> r
unpackSingIEx (SingEx x) k = k x

-- | Unpack an existential with an explicit singleton (CPS-style)
unpackSingEx 
  :: forall k (a :: k -> Type) (r :: Type)
   . SingEx a 
  -> (forall i. Sing i -> a i -> r) 
  -> r
unpackSingEx (SingEx x) k = k sing x

test1 :: Ex (Vec Int)
test1 = packEx (2 :> 1 :> 0 :> VNil)

_test2 :: Ex (Vec Int)
_test2 = packEx (3 :> 2 :> 1 :> 0 :> VNil)

_test3 :: Vec (Ex (Vec Int)) ('Succ ('Succ 'Zero)) 
_test3 = test1 :> _test2 :> VNil

_exVecSum :: Ex (Vec Int) -> Int
_exVecSum (Ex v) = go v where
  go :: forall (n :: Nat) . Vec Int n -> Int
  go VNil = 0
  go (x :> xs) = x + go xs

