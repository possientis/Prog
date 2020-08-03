module  Fol.Variable
    (   var
    )   where

import Fol.Syntax

var :: P v -> [v]
var (Bot)       = []
var (Elem x y)  = [x,y]
var (Imp p1 p2) = var p1 ++ var p2
var (All x p1)  = x : var p1

