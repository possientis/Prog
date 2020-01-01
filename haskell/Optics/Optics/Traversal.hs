module  Optics.Traversal
    (   Traversal   (..)
    )   where

import Optics.FunList

data Traversal s t a b = Traversal { extract :: s -> FunList a b t }
