module  Equal
    (   (===)
    )   where

import Set
import Incl

(===) :: Set -> Set -> Bool
(===) x y = x <== y && y <== x


