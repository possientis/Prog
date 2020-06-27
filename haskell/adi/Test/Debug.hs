module  Test.Debug
    (   main
    ,   e1, e2, e3
    )   where

import Macro
import Syntax
import Interpret

main :: IO ()
main = do
   evalIO e3

e1 :: Expr
e1 = eLam "x" (eVar "x") 

e2 :: Expr
e2 = eApp (eLam "x" (eLam "y" (eVar "x"))) (eNum 4)

e3 :: Expr 
e3 = eApp (eFac "f" "n") (eNum 5)
