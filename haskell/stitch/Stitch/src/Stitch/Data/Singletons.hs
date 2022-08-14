{-# LANGUAGE GADTs                #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Stitch.Data.Singletons 
  ( ShowSingVec 
  , SingI       (..)
  , SingKind    (..)
  , SNat        (..)
  , SVec        (..)
  , snatToInt
  , elemToSing
  ) where

import Data.Kind

import Stitch.Data.Nat
import Stitch.Data.Vec

-- Singleton class
class SingKind k where

  type Sing :: k -> Type

  fromSing :: forall (a :: k) . Sing a -> k

-- Singleton type for Nat
data SNat :: Nat -> Type where
  SZero :: SNat 'Zero
  SSucc :: SNat n -> SNat ('Succ n)

deriving instance Show (SNat n)

instance SingKind Nat where

  type Sing = SNat

  fromSing SZero      = Zero
  fromSing (SSucc n)  = Succ (fromSing n)

-- Singleton type for vectors
data SVec :: forall a n . Vec a n -> Type where
  SVNil :: SVec 'VNil
  (:%>) :: Sing a -> Sing as -> SVec (a ':> as)

infixr 5 :%>

deriving instance ShowSingVec v => Show (SVec v)

instance SingKind a => SingKind (Vec a n) where

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

instance SingKind a => SingI ('VNil :: Vec a 'Zero) where
  sing = SVNil

instance (SingI h, SingI t) => SingI (h ':> t) where
  sing = sing :%> sing

type family ShowSingVec (v :: Vec a n) :: Constraint where
  ShowSingVec 'VNil       = ()
  ShowSingVec (x ':> xs)  = (Show (Sing x), ShowSingVec xs) 

snatToInt :: SNat n -> Int
snatToInt SZero     = 0
snatToInt (SSucc n) = 1 + snatToInt n 

elemToSing
  :: forall (a :: Type) (n :: Nat) (xs :: Vec a n) (x :: a)
   . Elem xs x
  -> Sing xs
  -> Sing x
elemToSing  EZ (h :%> _) = h
elemToSing (ES e) (_ :%> t) = elemToSing e t

_test0 :: SNat 'Zero
_test0 = SZero

_test1 :: SNat ('Succ 'Zero)
_test1 = SSucc SZero

_replicate :: SNat n -> a -> Vec a n
_replicate SZero _    = VNil
_replicate (SSucc n)  x = x :> _replicate n x
