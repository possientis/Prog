module  Fol.Bound
    (   bnd
    )   where

import Fol.P

bnd :: P v -> [v]
bnd (Bot)       = []
bnd (Elem _ _)  = []
bnd (Imp p1 p2) = bnd p1 ++ bnd p2
bnd (All x p1)  = x : bnd p1


