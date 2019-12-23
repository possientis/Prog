{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE ExplicitForAll         #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module  Optics.Leq
    (   Leq     (..)
    ,   (:<)
    ,   lemma1
    ,   lemma2
    )   where

import Data.Proxy
import Data.Kind

import Optics.Nat
import Optics.Singleton

data Leq (n :: Nat) (m :: Nat) :: Type where
    Le_n :: forall (n :: Nat) . Leq n n 
    Le_S :: forall (n :: Nat) (m :: Nat) . Leq n m -> Leq n ('S m)

instance Eq (Leq n m) where
    (==) _ _  = True    -- all proofs are deemed equal

instance (KnownNat n, KnownNat m) => Show (Leq n m) where
    show _ = "_ :: Leq " 
           ++ (show $ natVal @ n Proxy)
           ++ " "
           ++ (show $ natVal @ m Proxy)

lemma1 :: forall (n :: Nat) . Leq n n
lemma1 = Le_n

lemma2 :: forall (n :: Nat) . Leq n ('S n)
lemma2 = Le_S Le_n

type family (n :: Nat) :< (m :: Nat) :: Bool where
    (:<)   _     'Z    = 'False
    (:<)  'Z    ('S _) = 'True
    (:<) ('S n) ('S m) = n :< m
