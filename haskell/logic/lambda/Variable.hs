{-# LANGUAGE ViewPatterns #-}

module Variable
  ( var
  ) where

import Expression
import Data.Set

var :: (Ord v) => Expression v -> Set v 
var (Variable x)  = fromList [x]
var (Apply p q)   = union (var p) (var q)
var (Lambda x p)  = insert x (var p)


