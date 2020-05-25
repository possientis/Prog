module  Incl
    (   (<==)
    )   where

import Set

(<==) :: Set -> Set -> Bool
(<==) Nil _  = True
(<==) (Cons x xs) ys = xs <== ys && any f (toList ys) where
    f :: Set -> Bool
    f y = x <== y && y <== x



