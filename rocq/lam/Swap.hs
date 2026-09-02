module  Swap
    (   swap
    )   where

import Term
import Permute

swap :: (Eq v) => v -> v -> P v -> P v
swap x y = fmap $ permute x y
