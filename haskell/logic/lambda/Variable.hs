module Variable
  ( var
  , free
  , bound
  ) where

import Formula
import Data.Set

var :: (Ord v) => Formula v -> Set v 
var (Variable x)  = singleton x
var (Apply p q)   = union (var p) (var q)
var (Lambda x p)  = insert x (var p)

free :: (Ord v) => Formula v -> Set v
free (Variable x) = singleton x
free (Apply p q)  = union (free p) (free q)
free (Lambda x p) = (free p) \\ singleton x 

bound :: (Ord v) => Formula v -> Set v
bound (Variable x)  = empty
bound (Apply p q)   = union (bound p) (bound q)
bound (Lambda x p)  = union (singleton x) (bound p)




