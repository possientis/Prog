module  Fol.Valid
    (   valid
    )   where

import Fol.P
import Fol.Free
import Fol.Subformula

-- TODO: find a good algorithm for this
valid :: (Eq v, Eq w) => (v -> w) -> P v -> Bool
valid f q = all cond xs where
    cond (p,x) = (f x) `elem` free (fmap f p) 
    xs = [(p,x)| p <- sub q, x <- free p]
