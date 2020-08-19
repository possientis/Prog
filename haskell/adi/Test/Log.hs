{-# LANGUAGE TypeApplications       #-}

module  Test.Log
    (   specLog
    )   where

import Test.Hspec

import DSL
import Eval
import Eval1
import Eval2

specLog :: Spec
specLog = describe "Testing Log for existing monads" $ do
    mapM_ testExpr $ zip [1..] [e1,e2,e3,e4,e5]

testExpr :: (Int, Expr) -> Spec
testExpr (n,e) = it ("Checked expression n. " ++ show n) $ do
    (evalLog @ Eval1) e `shouldBe` (evalLog @ Eval2) e

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

