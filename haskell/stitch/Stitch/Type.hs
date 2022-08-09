{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeInType       #-}

module  Stitch.Type
  ( Ty 
  , pattern Ty
  ) where

import Data.Kind
import Type.Reflection

import Stitch.Data.Exists

type Ty = Ex (TypeRep :: Type -> Type)

pattern Ty 
  :: forall k f
   . forall (i :: k)
   . f i 
  -> Ex f 
pattern Ty t = Ex t
{-# COMPLETE Ty #-}



