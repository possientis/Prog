{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}

module  Stitch.Shift
  ( --Shiftable (..)
  ) where

--import Data.Kind

--import Stitch.Data.Vec
--import Stitch.Exp

{-
class Shiftable (a :: forall n . Ctx n -> Type -> Type) where
  -- | Shift all de Bruijn indices to accommodate a new context prefix
  shifts   :: Length prefix -> a ctx ty -> a (prefix :++: ctx) ty

  -- | Shift a closed term into a context with bound variables; this
  -- can often be more efficient than the general case
  shifts0  :: a 'VNil ty -> a prefix ty

  -- | Lower de Bruijn indices if possible; fails if an index is too low
  unshifts :: Length prefix -> a (prefix :++: ctx) ty -> Maybe (a ctx ty)
-}
