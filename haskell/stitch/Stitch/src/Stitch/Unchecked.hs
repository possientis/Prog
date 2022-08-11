{-# LANGUAGE TypeInType   #-}

module Stitch.Unchecked
  ( UExp  (..)
  ) where

import Stitch.Data.Fin
import Stitch.Data.Nat

import Stitch.Op
import Stitch.Type

-- | Unchecked expression, indexed by the number of variables in scope
data UExp (n :: Nat)
  = UVar (Fin n)      -- ^ de Bruijn index for a variable
  | UGlobal String
  | ULam Ty (UExp ('Succ n))
  | UApp (UExp n) (UExp n)
  | ULet (UExp n) (UExp ('Succ n))
  | UArith (UExp n) UArithOp (UExp n)
  | UCond (UExp n) (UExp n) (UExp n) 
  | UFix (UExp n)
  | UIntE Int
  | UBoolE Bool
--  deriving Show
