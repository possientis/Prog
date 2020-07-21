module  Lam.ReplaceT
    (   (<-:)   -- 't <-: x' is [t/x]
    ,   replaceT
    )   where

import Lam.T

(<-:) :: (Eq v) => T v -> v -> (v -> T v)
(<-:) t x u 
    | u == x    = t
    | otherwise = Var u

replaceT :: (Eq v) => v -> T v -> (v -> T v)
replaceT x t = (t <-: x)    -- t in place of x


