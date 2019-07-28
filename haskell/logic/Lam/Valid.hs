module  Lam.Valid
    (   valid
    )   where

import Lam.T
import Lam.Free
import Lam.Subformula

-- TODO: find a good algorithm for this
valid :: (Eq v, Eq w) => (v -> w) -> T v -> Bool
valid f t = all cond xs where
    cond (s,x) = (f x) `elem` free (fmap f s) 
    xs = [(s,x)| s <- sub t, x <- free s]
