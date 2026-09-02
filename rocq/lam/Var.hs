module  Var
    (
    )   where

import Term

var :: P v -> [v]
var (Var x)     = [x]
var (App t1 t2) = var t1 ++ var t2
var (Lam x t1)  = x : var t1
