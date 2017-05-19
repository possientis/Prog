{-# LANGUAGE ViewPatterns #-}

module Variable
  ( var
  ) where

import LambdaCalculus
import Data.Set

var :: (LambdaCalculus m, Ord v) => m v -> Set v 
var (asType -> VariableType x)  = fromList [x]
var (asType -> ApplyType p q)   = union (var p) (var q)
var (asType -> LambdaType x p)  = insert x (var p)


