module AlphaEquiv
  ( alphaEq
  ) where

import Data.Functor ((<$>))
import Data.Set
import Formula
import Variable
import Substitution

alphaEq :: (Eq v, Ord v) => Formula v -> Formula v -> Bool
alphaEq (Variable x) (Variable x')  = (x == x')
alphaEq (Apply p q) (Apply p' q')   = alphaEq p p' && alphaEq q q'
alphaEq (Lambda x p) (Lambda x' p') = if (x == x') 
  then  alphaEq p p'
  else (not $ member x' $ free p) && alphaEq ((x<->x')<$>p) p'
alphaEq _ _                         = False


