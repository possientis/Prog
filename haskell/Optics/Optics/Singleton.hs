{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module  Optics.Singleton
    (   Sing        (..)
    ,   SingE       (..)  
    ,   SingI       (..)
    ,   SBool
    ,   SNat
    ,   KnownNat    (..)
    ,   natVal
    )   where

import Optics.Nat

data family Sing (a :: k) 


instance Eq (Sing a) where
    (==) _ _ = True

class SingE (a :: k) where
    type Demote a
    fromSing :: Sing a -> Demote a

class SingI a where
    sing :: Sing a

-- SBool
type SBool (a :: Bool) = Sing a

data instance Sing (a :: Bool) where
    STrue  :: Sing 'True
    SFalse :: Sing 'False 

instance Show (SBool a) where
    show = show . fromSing

instance SingE (a :: Bool) where
    type Demote a = Bool
    fromSing STrue  = True
    fromSing SFalse = False

--SNat
type SNat (a :: Nat) = Sing a

data instance Sing (a :: Nat) where
    SZ :: Sing 'Z
    SS :: Sing n -> Sing ('S n)

instance Show (SNat n) where
    show = show . fromSing

instance SingE (n :: Nat) where
    type Demote n = Nat
    fromSing SZ = Z
    fromSing (SS n) = S (fromSing n)

instance SingI 'Z where
    sing = SZ 

instance (SingI n) => SingI ('S n) where 
    sing = SS sing

class KnownNat (n :: Nat) where
    natSing :: SNat n

instance KnownNat 'Z where
    natSing = SZ

instance (KnownNat n) => KnownNat ('S n) where
    natSing = SS natSing

natVal :: forall n proxy . KnownNat n => proxy n -> Nat
natVal _ = fromSing (natSing @n)


