{-# LANGUAGE ViewPatterns #-}
module SubFormula
  ( sub
  , (<=:)
  ) where

import Formula
import Data.Set

-- returns the set of subformulas
sub :: (Ord v) => Formula v -> Set (Formula v)
sub q@(Variable x)  = singleton q
sub r@(Apply p q)   = unions [ singleton r, sub p, sub q ]
sub q@(Lambda x p)  = union (singleton q) (sub p)

-- relation 'is a subformula of'
(<=:) :: (Ord v) => Formula v -> Formula v -> Bool
(<=:) p q = member p (sub q)
