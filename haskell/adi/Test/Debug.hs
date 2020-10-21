{-# LANGUAGE TypeApplications       #-}

module  Test.Debug
    (   main
    ,   e1, e2, e3, e4, e5, e6, e7, e8, e9, e10
    ,   e11, e12, e13
    )   where

import DSL
import Eval     as E
import Eval1
--import Pretty
--import Reduce

main :: IO ()
main = evalIO @ Eval1 e13
{-
main = do
    let e = e5
    putStrLn $ "e       = " ++ showExpr e
    putStrLn $ "eval e  = " ++ show (E.eval @ Eval1 e) 
    putStrLn "Reduction:"
    mapM_ (putStrLn . showExpr) $ trace e
-}

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

e10 :: Expr
e10 = eCase (eNat 1) (eNum 0) "a" (eVar "a")

e11 :: Expr
e11 = eNat 0

-- reduces for ever
e12 :: Expr
e12 = eRec "x" (eSuc (eVar "x"))

e13 :: Expr
e13 = eMul (eAdd (eNum 3) (eNum 4)) (eNum 9)



