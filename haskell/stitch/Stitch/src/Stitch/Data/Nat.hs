{-# LANGUAGE TypeFamilies   #-}
{-# LANGUAGE TypeInType     #-}
{-# LANGUAGE TypeOperators  #-}

module Stitch.Data.Nat 
  ( Nat   (..)
  , (:+:)
  ) where

data Nat = Zero | Succ Nat
  deriving Show

type family (n :: Nat) :+: (m :: Nat) where
  'Zero   :+: m = m
  'Succ n :+: m = 'Succ (n :+: m)
