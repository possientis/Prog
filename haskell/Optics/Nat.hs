{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module  Optics.Nat
    (   Nat         (..)
    ,   SNat        (..)
    ,   (:<)
    ,   Leq         (..)
    ,   lemma1
    ,   lemma2
    )   where

import Data.Kind

data Nat = Z | S Nat

type family (n :: Nat) :< (m :: Nat) :: Bool 
type instance   _    :<  'Z    = 'False
type instance  'Z    :< ('S _) = 'True
type instance ('S n) :< ('S m) = n :< m

data Leq (n :: Nat) (m :: Nat) :: Type where
    Le_n :: forall (n :: Nat) . Leq n n 
    Le_S :: forall (n :: Nat) (m :: Nat) . Leq n m -> Leq n ('S m)

lemma1 :: forall (n :: Nat) . Leq n n
lemma1 = Le_n

lemma2 :: forall (n :: Nat) . Leq n ('S n)
lemma2 = Le_S Le_n

-- SNat 'Z has only one instance
-- SNat ('S 'Z) has only one instance
-- ...
data SNat (n :: Nat) :: Type where
    SZ :: SNat 'Z
    SS :: forall (n :: Nat) . SNat n -> SNat ('S n)






