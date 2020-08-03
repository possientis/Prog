module  Fol.Dmap
    (   dmap
    )   where

import Fol.Syntax


dmap :: (Eq v) => (v -> w) -> (v -> w) -> P v -> P w
dmap f g p = dmap_ f g p []

dmap_ :: (Eq v ) => (v -> w) -> (v -> w) -> P v -> [v] -> P w
dmap_ _ _ (Bot)       _  = Bot
dmap_ f g (Elem x y)  xs = Elem (h_ f g xs x) (h_ f g xs y)
dmap_ f g (Imp p1 p2) xs = Imp (dmap_ f g p1 xs) (dmap_ f g p2 xs) 
dmap_ f g (All x p1)  xs = All (g x) (dmap_ f g p1 (x:xs))


h_ :: (Eq v) => (v -> w) -> (v -> w) -> [v] -> v -> w
h_ f g xs x = if x `elem` xs then g x else f x
