module  Fol.Haskell.Free
    (   free
    )   where

import Haskell.Remove
import Fol.Haskell.P

free :: (Eq v) => P v -> [v]
free (Bot)       = []
free (Elem x y)  = [x,y]
free (Imp p1 p2) = free p1 ++ free p2
free (All x p1)  = remove x (free p1)