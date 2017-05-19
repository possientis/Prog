{-# LANGUAGE ViewPatterns #-}

module Variable
  ( var
  ) where

import FirstOrder
import Data.Set

var :: (FirstOrder m, Ord v) => m v -> Set v 
var (asType -> BelongType x y)  = fromList [x,y]
var (asType -> BotType)         = empty
var (asType -> ImplyType p q)   = union (var p) (var q)
var (asType -> ForallType x p)  = insert x (var p)


