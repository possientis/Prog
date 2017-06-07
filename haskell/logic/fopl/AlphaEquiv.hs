module AlphaEquiv
  ( alphaEq
  ) where

import Data.Set
import Formula
import Variable
import Substitution

alphaEq :: (Eq v, Ord v) => Formula v -> Formula v -> Bool
alphaEq (Belong x y) (Belong x' y') = (x == x') && (y == y')
alphaEq (Bot) (Bot)                 = True
alphaEq (Imply p q) (Imply p' q')   = alphaEq p p' && alphaEq q q'
alphaEq (Forall x p) (Forall x' p') = if (x == x') 
  then  alphaEq p p'
  else not $ member x' (free p) && alphaEq ((x<->x')<$>p) p'
alphaEq _ _                         = False


