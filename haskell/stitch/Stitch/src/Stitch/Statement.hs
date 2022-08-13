{-# LANGUAGE TypeInType #-}

module  Stitch.Statement
  ( Statement (..)
  ) where

import Text.PrettyPrint.ANSI.Leijen

import Stitch.Data.Nat
import Stitch.Unchecked

-- | A statement can either be a bare expression, which will be evaluated,
-- or an assignment to a global variable.
data Statement 
  = BareExp (UExp 'Zero)
  | NewGlobal String (UExp 'Zero)
  deriving Show

instance Pretty Statement where
  pretty (BareExp e)     = pretty e
  pretty (NewGlobal v e) = text v <+> char '=' <+> pretty e

