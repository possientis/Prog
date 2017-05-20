{-# LANGUAGE ViewPatterns #-}

module Variable
  ( var
  ) where

import Data.Set
import Formula

var :: (Ord v) => Formula v -> Set v 
var (Belong x y)  = fromList [x,y]
var (Bot)         = empty
var (Imply p q)   = union (var p) (var q)
var (Forall x p)  = insert x (var p)


