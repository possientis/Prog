{-# LANGUAGE ViewPatterns #-}

module Variable
  ( var
  , free
  , bound
  ) where

import Data.Set
import Formula

var :: (Ord v) => Formula v -> Set v 
var (Belong x y)  = fromList [x,y]
var (Bot)         = empty
var (Imply p q)   = union (var p) (var q)
var (Forall x p)  = insert x (var p)

free :: (Ord v) => Formula v -> Set v
free (Belong x y) = fromList [x,y]
free (Bot)        = empty
free (Imply p q)  = union (free p) (free q)
free (Forall x p) = (free p) \\ singleton x 

bound :: (Ord v) => Formula v -> Set v
bound (Belong x y)  = empty
bound (Bot)         = empty
bound (Imply p q)   = union (bound p) (bound q)
bound (Forall x p)  = union (singleton x) (bound p)

