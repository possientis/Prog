module  Fol.Dmap
    (   dmap
    ,   dmap_
    )   where

import Fol.Syntax


dmap :: (Eq v) => (v -> w) -> (v -> w) -> P v -> P w
dmap f g p = dmap_ f g [] p

dmap_ :: (Eq v ) => (v -> w) -> (v -> w) -> [v] -> P v -> P w
dmap_ _ _ _ (Bot)        = Bot
dmap_ f g xs (Elem x y)  = Elem (h_ f g xs x) (h_ f g xs y)
dmap_ f g xs (Imp p1 p2) = Imp (dmap_ f g xs p1) (dmap_ f g xs p2) 
dmap_ f g xs (All x p1)  = All (g x) (dmap_ f g (x:xs) p1)

h_ :: (Eq v) => (v -> w) -> (v -> w) -> [v] -> v -> w
h_ f g xs x = if x `elem` xs then g x else f x
