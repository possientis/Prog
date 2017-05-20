{-# LANGUAGE ViewPatterns #-}
module SubFormula
  ( sub
  ) where

import Formula
import Data.Set

sub :: (Ord v) => Formula v -> Set (Formula v)
sub q@(Belong x y)  = singleton q
sub q@(Bot)         = singleton q
sub r@(Imply p q)   = unions [ singleton q, sub p, sub q ]
sub q@(Forall x p)  = union (singleton q) (sub p)
