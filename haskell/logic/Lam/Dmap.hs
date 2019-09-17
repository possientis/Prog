module  Lam.Dmap
    (   dmap
    )   where

import Lam.T

h_ :: (Eq v) => (v -> w) -> (v -> w) -> [v] -> v -> w
h_ f g xs x = if x `elem` xs then g x else f x


dmap :: (Eq v ) => (v -> w) -> (v -> w) -> T v -> [v] -> T w
dmap f g (Var x)     xs = Var (h_ f g xs x)
dmap f g (App t1 t2) xs = App (dmap f g t1 xs) (dmap f g t2 xs) 
dmap f g (Lam x t1)  xs = Lam (g x) (dmap f g t1 (x:xs))
