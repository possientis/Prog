module  Fol.Order
    (   ord
    )   where

import Fol.P

ord :: P v -> Integer
ord Bot         = 1
ord (Elem _ _)  = 0
ord (Imp p1 p2) = 1 + max (ord p1) (ord p2)
ord (All _ p1)  = 1 + ord p1
