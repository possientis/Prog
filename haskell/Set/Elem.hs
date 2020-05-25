module  Elem
    (   (<:)
    )   where

import Set
import Incl

(<:) :: Set -> Set -> Bool
(<:) x y = (Cons x Nil) <== y

