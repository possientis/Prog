module  Test.Eval
    (   specEval
    )   where


import Op
import Macro
import Value
import Syntax
import Interpret

import Test.Hspec
import Test.QuickCheck

specEval :: Spec
specEval = describe "Checking the Eval module ..." $ do
    specENum
    specEBool
    specEOpAdd
    specEOpMul
    specEOpSub
    specEOpDiv
    specEIfZero
    specEIfNZero
    specEApp
    specERec
    specSum1
    specSum2

specENum :: Spec
specENum = it "Checked eval for ENum in empty environment" $ do
    property $ propENum

specEBool :: Spec
specEBool = it "Checked eval for EBool in empty environment" $ do
    property $ propEBool

specEOpAdd :: Spec 
specEOpAdd = it "Checked eval for n + m" $ do
    property $ propEOpAdd

specEOpMul :: Spec 
specEOpMul = it "Checked eval for n * m" $ do
    property $ propEOpMul

specEOpSub :: Spec 
specEOpSub = it "Checked eval for n - m" $ do
    property $ propEOpSub

specEOpDiv :: Spec 
specEOpDiv = it "Checked eval for n `div` m" $ do
    property $ propEOpDiv

specEIfZero :: Spec
specEIfZero = it "Checked eval for if 0 n m" $ do
    property $ propEIfZero

specEIfNZero :: Spec
specEIfNZero = it "Checked eval for if nz n m" $ do
    property $ propEIfNZero

specEApp :: Spec
specEApp = it "Checked eval for (\\x -> x^2) n" $ do
    property $ propEApp

specERec :: Spec
specERec = it "Checked eval for fix f = fac" $ do
    property $ propERec

specSum1 :: Spec
specSum1 = it "Checked eval for (\\x y -> x + y) n m" $ do
    property $ propSum1 

specSum2 :: Spec
specSum2 = it "Checked eval for (\\x x -> x + x) n m" $ do
    property $ propSum2 

propENum :: Integer -> Bool
propENum n = num (eval (eNum n)) == Just n  

propEBool :: Bool -> Bool
propEBool b = bool (eval (eBool b)) == Just b 

propEOpAdd :: Integer -> Integer -> Bool
propEOpAdd n m = num (eval (eOp add [(eNum n),(eNum m)])) == Just (n + m)
 
propEOpMul :: Integer -> Integer -> Bool
propEOpMul n m = num (eval (eOp mul [(eNum n),(eNum m)])) == Just (n * m)

propEOpSub :: Integer -> Integer -> Bool
propEOpSub n m = num (eval (eOp sub [(eNum n),(eNum m)])) == Just (n - m)

propEOpDiv :: Integer -> Integer -> Bool
propEOpDiv n m = m == 0 || 
    num (eval (eOp dvd [(eNum n),(eNum m)])) == Just (n `div` m)

propEIfZero :: Integer -> Integer -> Bool
propEIfZero n m = num (eval (eIf (eNum 0) (eNum n) (eNum m))) == Just n

propEIfNZero :: Integer -> Integer -> Integer -> Bool
propEIfNZero nz n m = if nz == 0 then True else
    num (eval (eIf (eNum nz) (eNum n) (eNum m))) == Just m

propEApp :: Integer -> String -> Bool
propEApp n s = s == "" || 
    num (eval 
            (eApp 
                (eLam s (eOp mul [(eVar s),(eVar s)]))
                (eNum n))) == Just (n * n)

propERec :: Integer -> String -> String -> Bool
propERec m f n  = f == "" || n == "" || f == n || m < 0 ||
    num (eval (eApp (eFac f n) (eNum m))) == Just (product [1..m])

propSum1 :: String -> String -> Integer -> Integer -> Bool
propSum1 x y n m = x == "" || y == "" || x /= y ||  
    num (eval (eApp (eApp (eSum x y) (eNum n)) (eNum m))) == Just (n + m)

propSum2 :: String -> Integer -> Integer -> Bool
propSum2 x n m = x == "" || 
    num (eval (eApp (eApp (eSum x x) (eNum n)) (eNum m))) == Just (m + m)
