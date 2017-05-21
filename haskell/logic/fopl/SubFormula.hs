{-# LANGUAGE ViewPatterns #-}
module SubFormula
  ( sub
  , (<=:)
  ) where

import Formula
import Data.Set

-- returns the set of subformulas
sub :: (Ord v) => Formula v -> Set (Formula v)
sub q@(Belong x y)  = singleton q
sub q@(Bot)         = singleton q
sub r@(Imply p q)   = unions [ singleton r, sub p, sub q ]
sub q@(Forall x p)  = union (singleton q) (sub p)

-- relation 'is a subformula of'
(<=:) :: (Ord v) => Formula v -> Formula v -> Bool
(<=:) p q = member p (sub q)
