module  Lam.Bound
    (   bnd
    )   where

import Lam.T

bnd :: T v -> [v]
bnd (Var _)     = []
bnd (App t1 t2) = bnd t1 ++ bnd t2
bnd (Lam x t1)  = x : bnd t1
