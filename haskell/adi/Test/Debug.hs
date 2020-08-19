{-# LANGUAGE TypeApplications       #-}

module  Test.Debug
    (   main
    ,   e1, e2, e3, e4, e5
    )   where

import DSL
import Eval
import Eval2

main :: IO ()
main = mapM_ (evalIO @ Eval2) [e1,e2,e3,e4,e5]

e1 :: Expr
e1 = eLam "x" (eVar "x") 

e2 :: Expr
e2 = eApp (eLam "x" (eLam "y" (eVar "x"))) (eNum 4)

e3 :: Expr 
e3 = eApp eFac (eNum 5)

e4 :: Expr
e4 = eDiv (eNum 0) (eNum 1)

e5 :: Expr
e5 = eDiv (eNum 1) (eNum 0) -- division by zero

