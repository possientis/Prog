module  Lam.Dmap
    (   dmap
    )   where

import Lam.Syntax

dmap :: (Eq v) => (v -> w) -> (v -> w) -> T v -> T w
dmap f g t = dmap_ f g t []

dmap_ :: (Eq v) => (v -> w) -> (v -> w) -> T v -> [v] -> T w
dmap_ f g (Var x)     xs = Var (h_ f g xs x)
dmap_ f g (App t1 t2) xs = App (dmap_ f g t1 xs) (dmap_ f g t2 xs) 
dmap_ f g (Lam x t1)  xs = Lam (g x) (dmap_ f g t1 (x:xs))


h_ :: (Eq v) => (v -> w) -> (v -> w) -> [v] -> v -> w
h_ f g xs x = if x `elem` xs then g x else f x
