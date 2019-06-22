module Admissible
  ( isAdmissibleFor
  ) where

import Formula
import Variable
import Valid
import Prelude hiding (map, null, filter)
import Data.Set

isAdmissibleFor :: (Eq v, Ord v) => (v -> v) -> Formula v -> Bool
isAdmissibleFor f p   =   isValidFor f p 
                      &&  (null $ filter pred (free p)) 
  where pred x = (f x /= x)
 
