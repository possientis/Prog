module  Fol.Subformula
    (   sub
    ,   (<<=)
    )   where

import Fol.P

sub :: P v -> [P v]
sub Bot         = [Bot]
sub (Elem x y)  = [Elem x y]
sub (Imp p1 p2) = (Imp p1 p2) : (sub p1 ++ sub p2)
sub (All x p1)  = (All x p1)  : sub p1

(<<=) :: (Eq v) => P v -> P v -> Bool
(<<=) t s = t `elem` sub s