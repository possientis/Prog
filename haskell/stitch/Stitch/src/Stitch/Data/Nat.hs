{-# LANGUAGE TypeFamilies   #-}
{-# LANGUAGE TypeInType     #-}
{-# LANGUAGE TypeOperators  #-}

module Stitch.Data.Nat 
  ( Nat   (..)
  , (:+:)
  ) where

data Nat = Zero | Succ Nat
  deriving Show

type family n :+: m where
  'Zero   :+: m = m
  'Succ n :+: m = 'Succ (n :+: m)

