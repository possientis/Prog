{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE ExplicitForAll         #-}

module  Optics.Leq
    (   Leq     (..)
    ,   (:<)
    ,   lemma1
    ,   lemma2
    )   where

import Data.Kind

import Optics.Nat

data Leq (n :: Nat) (m :: Nat) :: Type where
    Le_n :: forall (n :: Nat) . Leq n n 
    Le_S :: forall (n :: Nat) (m :: Nat) . Leq n m -> Leq n ('S m)

lemma1 :: forall (n :: Nat) . Leq n n
lemma1 = Le_n

lemma2 :: forall (n :: Nat) . Leq n ('S n)
lemma2 = Le_S Le_n

type family (n :: Nat) :< (m :: Nat) :: Bool where
    (:<)   _     'Z    = 'False
    (:<)  'Z    ('S _) = 'True
    (:<) ('S n) ('S m) = n :< m
