module  Lam.Order
    (   ord
    )   where

import Lam.T

ord :: T v -> Integer
ord (Var _)     = 0
ord (App t1 t2) = 1 + max (ord t1) (ord t2) 
ord (Lam _ t1)  = 1 + ord t1
