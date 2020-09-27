{-# LANGUAGE TypeApplications       #-}

module  Test.Debug
    (   main
    ,   e1, e2, e3, e4, e5, e6, e7, e8, e9
    )   where

import DSL
--import Eval
--import Eval2
import Pretty
import Reduce

main :: IO ()
main = do
    putStrLn $ "e8 = " ++ showExpr e8
    putStrLn $ "eval e8 = " ++ showExpr (eval e8)
    putStrLn $ "e9 = " ++ showExpr e9
    putStrLn $ "eval e9 = " ++ showExpr (eval e9)
    print $ eval e8 == eval e9

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

e6 :: Expr
e6 = eApp2 eMulNat (eNat 2) (eNat 2)

e7 :: Expr
e7 = eApp eFromNat (eApp eFacNat (eNat 5))

e8 :: Expr
e8 = eSuc (eNat 5)

e9 :: Expr
e9 = eNat 6
