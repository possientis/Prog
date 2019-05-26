module  Lam.Haskell.Variable
    (   var
    )   where

import Lam.Haskell.T

var :: T v -> [v]
var (Var x)     = [x]
var (App t1 t2) = var t1 ++ var t2
var (Lam x t1)  = x : var t1

