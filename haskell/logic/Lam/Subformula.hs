module  Lam.Subformula
    (   sub
    )   where

import Lam.T

sub :: T v -> [T v]
sub (Var x)     = [Var x]
sub (App t1 t2) = (App t1 t2) : (sub t1 ++ sub t2)
sub (Lam x t1)  = (Lam x t1)  : sub t1
