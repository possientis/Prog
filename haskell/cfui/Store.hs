{-# LANGUAGE InstanceSigs           #-}

module  Store
    (   Store (..)
    )   where

import Control.Comonad

data Store s a = Store (s -> a) s

instance Functor (Store s) where
  fmap f (Store g s) = Store (f . g) s

instance Comonad (Store s) where
  extract :: Store s a -> a                       -- Just a reminder 
  extract (Store f s) = f s
  duplicate :: Store s a -> Store s (Store s a)   -- Just a reminder 
  duplicate (Store f s) = Store (Store f) s


