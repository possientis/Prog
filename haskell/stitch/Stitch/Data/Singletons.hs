{-# LANGUAGE GADTs              #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeInType         #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE UndecidableInstances #-}

module Stitch.Data.Singletons 
  ( ShowSingVec 
  , SingI       (..)
  , SingKind    (..)
  , SNat        (..)
  , SVec        (..)
  , snatToInt
  ) where

import Data.Kind

import Stitch.Data.Nat
import Stitch.Data.Vec

-- Singleton type for vectors
data SVec :: forall (a :: Type) (n :: Nat) . Vec n a -> Type where
  SVNil :: SVec 'VNil
  (:%>) :: Sing a -> Sing as -> SVec (a ':> as)

infixr 5 :%>

deriving instance ShowSingVec v => Show (SVec v)

-- Singleton type for Nat
data SNat :: Nat -> Type where
  SZero :: SNat 'Zero
  SSucc :: SNat n -> SNat ('Succ n)

deriving instance Show (SNat n)

-- Singleton class
class SingKind k where

  type Sing :: k -> Type

  fromSing :: Sing (a :: k) -> k

instance SingKind Nat where

  type Sing = SNat

  fromSing SZero      = Zero
  fromSing (SSucc n)  = Succ (fromSing n)

instance SingKind a => SingKind (Vec n a) where

  type Sing = SVec
  
  fromSing SVNil  = VNil
  fromSing (h :%> t) = fromSing h :> fromSing t


-- Implicit singleton
class SingKind k => SingI (a :: k) where
  sing :: Sing a

instance SingI 'Zero where
  sing = SZero

instance SingI n => SingI ('Succ n) where
  sing = SSucc sing

instance SingKind a => SingI ('VNil :: Vec 'Zero a) where
  sing = SVNil

instance (SingI h, SingI t) => SingI (h ':> t) where
  sing = sing :%> sing

snatToInt :: SNat n -> Int
snatToInt SZero     = 0
snatToInt (SSucc n) = 1 + snatToInt n 

_test0 :: SNat 'Zero
_test0 = SZero

_test1 :: SNat ('Succ 'Zero)
_test1 = SSucc SZero

_replicate :: SNat n -> a -> Vec n a
_replicate SZero _    = VNil
_replicate (SSucc n)  x = x :> _replicate n x

_test2 :: SVec 'VNil
_test2 = SVNil

_test3 :: SVec ('Zero ':> 'VNil)
_test3 = sing

type family ShowSingVec (v :: Vec n a) :: Constraint where
  ShowSingVec 'VNil       = ()
  ShowSingVec (x ':> xs)  = (Show (Sing x), ShowSingVec xs) 
