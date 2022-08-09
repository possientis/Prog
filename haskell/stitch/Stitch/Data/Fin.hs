{-# LANGUAGE GADTs              #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeInType         #-}

module Stitch.Data.Fin
  ( Fin (..)
  , finToInt
  ) where

import Data.Kind

import Stitch.Data.Nat

data Fin :: Nat -> Type where
  FZ :: Fin ('Succ n)
  FS :: Fin n -> Fin ('Succ n)  

deriving instance Show (Fin a)

finToInt :: Fin n -> Int
finToInt FZ = 0
finToInt (FS n) = 1 + finToInt n

_test1 :: Int
_test1 = finToInt (FZ :: Fin ('Succ 'Zero))

_test2 :: Int
_test2 = finToInt (FZ :: Fin ('Succ ('Succ 'Zero)))

_test3 :: Int
_test3 = finToInt (FS FZ :: Fin ('Succ ('Succ 'Zero)))


