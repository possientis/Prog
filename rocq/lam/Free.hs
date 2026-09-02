module  Free
    (   free
    )   where

import Term

free :: (Eq v) => P v -> [v]
free (Var x)     = [x]
free (App t1 t2) = free t1 ++ free t2 
free (Lam x t1)  = remove x $ free t1


remove :: (Eq a) => a -> [a] -> [a]
remove x = filter (/=x)

