module  Alpha 
    (   alpha
    )   where

import Term
import Free
import Swap

alpha :: (Eq v) => P v -> P v -> Bool
alpha (Var x) (Var y)                   = x == y 
alpha (App t1 t2) (App t1' t2')         = alpha t1 t1' && alpha t2 t2'
alpha (Lam x t1) (Lam y t1') | x == y   = alpha t1 t1'
alpha (Lam x t1) (Lam y t1') | x /= y   = not (y `elem` free t1) 
                                       && alpha t1' (swap x y t1)  
alpha _ _                               = False

t1 :: P Int
t1 = Lam 0 (Lam 1 (App (Var 0) (Var 1)))

t2 :: P Int
t2 = Lam 1 (Lam 0 (App (Var 1) (Var 0)))

main :: IO ()
main = do
    print $ alpha t1 t2


   
