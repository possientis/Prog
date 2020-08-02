module  Lam.Free
    (   free
    )   where

import Lam.T
import List.Remove

free :: (Eq v) => T v -> [v]
free (Var x)     = [x]
free (App t1 t2) = free t1 ++ free t2
free (Lam x t1)  = remove x (free t1)
