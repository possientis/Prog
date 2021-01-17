{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module  Store
    (   Store (..)
    ,   State (..)
    )   where

import Control.Comonad

import State
import Pairing

data Store s a = Store (s -> a) s

instance Functor (Store s) where
  fmap f (Store g s) = Store (f . g) s

instance Comonad (Store s) where
  extract :: Store s a -> a                       -- Just a reminder 
  extract (Store f s) = f s
  duplicate :: Store s a -> Store s (Store s a)   -- Just a reminder 
  duplicate (Store f s) = Store (Store f) s

instance Pairing (State s) (Store s) where
  pair :: (a -> b -> c) -> State s a -> Store s b -> c
  pair op (State f) (Store g s) = let (a,s') = f s in op a (g s')

