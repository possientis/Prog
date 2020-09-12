module  Lam.Dmap
    (   dmap
    ,   dmap_
    )   where

import Lam.Syntax

dmap :: (Eq v) => (v -> w) -> (v -> w) -> T v -> T w
dmap f g t = dmap_ f g [] t

dmap_ :: (Eq v) => (v -> w) -> (v -> w) -> [v] -> T v -> T w
dmap_ f g xs (Var x)     = Var (h_ f g xs x)
dmap_ f g xs (App t1 t2) = App (dmap_ f g xs t1) (dmap_ f g xs t2) 
dmap_ f g xs (Lam x t1)  = Lam (g x) (dmap_ f g (x:xs) t1)

h_ :: (Eq v) => (v -> w) -> (v -> w) -> [v] -> v -> w
h_ f g xs x = if x `elem` xs then g x else f x
