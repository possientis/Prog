module  ZF.Prop
  ( Prop  (..)
  , (&)
  , (==>)
  ) where

import ZF.Var

data Prop
  = PVar Var
  | Bot
  | In Var Var
  | Imp Prop Prop
  | All Var Prop

(&) :: Var -> Var -> Prop
(&) = In

(==>) :: Prop -> Prop -> Prop
(==>) = Imp
