module  Lam.Replace
    (   replace'
    )   where

import Lam.T

replace' :: (Eq v) => v -> T v -> v -> T v
replace' x t u
    | u == x    = t
    | otherwise = Var u 
