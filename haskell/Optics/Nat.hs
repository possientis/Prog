{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE UndecidableInstances   #-}

module  Optics.Nat
    (   Nat         (..)
    ,   SNat        (..)
    ,   SBool       (..)
    ,   (:<)
    ,   If
    ,   Plus
    ,   IsEven
    ,   NextEven
    ,   sPlus
    ,   sIsEven
    ,   isEven
    ,   nextEven
    ,   Leq         (..)
    ,   lemma1
    ,   lemma2
    )   where

import Data.Kind

data Nat = Z | S Nat

isEven :: Nat -> Bool 
isEven Z = True
isEven (S Z) = False
isEven (S (S n)) = isEven n

nextEven :: Nat -> Nat 
nextEven n = if isEven n then n else S n 

-- SNat 'Z has only one instance
-- SNat ('S 'Z) has only one instance
-- ...
data SNat (n :: Nat) :: Type where
    SZ :: SNat 'Z
    SS :: forall (n :: Nat) . SNat n -> SNat ('S n)

data SBool (b :: Bool) :: Type where
    STrue  :: SBool 'True
    SFalse :: SBool 'False 


type family (n :: Nat) :< (m :: Nat) :: Bool 
type instance   _    :<  'Z    = 'False
type instance  'Z    :< ('S _) = 'True
type instance ('S n) :< ('S m) = n :< m


type family   Plus (n :: Nat) (m :: Nat) :: Nat
type instance Plus  'Z    m = m
type instance Plus ('S n) m = 'S (Plus n m)

sPlus :: SNat n -> SNat m -> SNat (Plus n m)
sPlus  SZ    m = m
sPlus (SS n) m = SS (sPlus n m) 

type family   IsEven (n :: Nat) :: Bool
type instance IsEven  'Z = 'True
type instance IsEven ('S 'Z) = 'False 
type instance IsEven ('S ('S n)) = IsEven n

sIsEven :: SNat n -> SBool (IsEven n)
sIsEven SZ = STrue
sIsEven (SS SZ) = SFalse
sIsEven (SS (SS n)) = sIsEven n

type family   If (b :: Bool) (x :: k) (y :: k) :: k
type instance If 'True  x _ = x
type instance If 'False _ y = y

type family   NextEven (n :: Nat) :: Nat
type instance NextEven n = If (IsEven n) n ('S n)


data Leq (n :: Nat) (m :: Nat) :: Type where
    Le_n :: forall (n :: Nat) . Leq n n 
    Le_S :: forall (n :: Nat) (m :: Nat) . Leq n m -> Leq n ('S m)

lemma1 :: forall (n :: Nat) . Leq n n
lemma1 = Le_n

lemma2 :: forall (n :: Nat) . Leq n ('S n)
lemma2 = Le_S Le_n






