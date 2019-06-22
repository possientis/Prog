module Valid
  ( isValidFor
  ) where

import Formula
import Variable
import Prelude hiding (map, null, filter)
import Data.Set

-- f : v -> w is valid for Ax.p if and only if it is valid for p, and for 
-- all u in (free Ax.p) we have f u /= f x.
isValidFor :: (Eq v, Ord v, Eq w, Ord w) => (v -> w) -> Formula v -> Bool
isValidFor f (Belong x y)   = True
isValidFor f (Bot)          = True
isValidFor f (Imply p q)    = isValidFor f p && isValidFor f q
isValidFor f q@(Forall x p) = isValidFor f p &&
  (null $ filter (== f x) (map f (free q))) 
