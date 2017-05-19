{-# LANGUAGE ViewPatterns #-}
module SubFormula
  ( sub
  ) where

import FirstOrder
import Data.Set

sub :: (FirstOrder m) => m v -> Bool
sub (asType -> BelongType x y)  = (belong x y) == (belong x y)
