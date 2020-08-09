module  Test.Debug
    (   main
    ,   e1, e2, e3, e4
    )   where


import DSL
import Eval1
import Interpret

main :: IO ()
main = do
   evalIO e5

evalIO :: Expr -> IO ()
evalIO e = do
    let (res,logs) = runEval1 $ eval e
    mapM_ putStrLn logs
    print res
 
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

