module  Test.Eval
    (   specEval
    )   where


import Op
import Macro
import Value
import Syntax
import Interpret

import Prelude          hiding (and, or)
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
    specEOpAnd
    specEOpOr
    specEOpImp
    specEOpNot
    specEOpLe
    specEOpEq
    specEIfZero
    specEIfNZero
    specEApp
    specERec
    specEZero
    specESuc
    specENat
    specECaseZero
    specECaseSuc
    specSum1
    specSum2

specENum :: Spec
specENum = it "Checked eval for ENum in empty environment" $ do
    property $ propENum

specEBool :: Spec
specEBool = it "Checked eval for EBool in empty environment" $ do
    property $ propEBool

specEOpAdd :: Spec 
specEOpAdd = it "Checked eval for (n + m)" $ do
    property $ propEOpAdd

specEOpMul :: Spec 
specEOpMul = it "Checked eval for (n * m)" $ do
    property $ propEOpMul

specEOpSub :: Spec 
specEOpSub = it "Checked eval for (n - m)" $ do
    property $ propEOpSub

specEOpDiv :: Spec 
specEOpDiv = it "Checked eval for (n `div` m)" $ do
    property $ propEOpDiv

specEOpAnd :: Spec 
specEOpAnd = it "Checked eval for (b and b')" $ do
    property $ propEOpAnd

specEOpOr :: Spec 
specEOpOr = it "Checked eval for (b or b')" $ do
    property $ propEOpOr

specEOpImp :: Spec 
specEOpImp = it "Checked eval for (b imp b')" $ do
    property $ propEOpImp

specEOpNot :: Spec 
specEOpNot = it "Checked eval for (not b)'" $ do
    property $ propEOpNot

specEOpLe :: Spec 
specEOpLe = it "Checked eval for (n <= m)'" $ do
    property $ propEOpLe

specEOpEq :: Spec 
specEOpEq = it "Checked eval for (n == m)'" $ do
    property $ propEOpEq

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

specEZero :: Spec
specEZero = it "Checked eval for eZero" $ do
    property $ propEZero

specESuc :: Spec
specESuc = it "Checked eval for eSuc" $ do
    property $ propESuc

specENat :: Spec
specENat = it "Checked eval for eNat" $ do
    property $ propENat

specECaseZero :: Spec
specECaseZero = it "Checked eval for eCase zero" $ do   
    property $ propECaseZero

specECaseSuc :: Spec
specECaseSuc = it "Checked eval for eCase suc" $ do   
    property $ propECaseSuc

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
propEOpAdd n m = num (eval (eOp oAdd [(eNum n),(eNum m)])) == Just (n + m)
 
propEOpMul :: Integer -> Integer -> Bool
propEOpMul n m = num (eval (eOp oMul [(eNum n),(eNum m)])) == Just (n * m)

propEOpSub :: Integer -> Integer -> Bool
propEOpSub n m = num (eval (eOp oSub [(eNum n),(eNum m)])) == Just (n - m)

propEOpDiv :: Integer -> Integer -> Bool
propEOpDiv n m = m == 0 || 
    num (eval (eOp oDiv [(eNum n),(eNum m)])) == Just (n `div` m)

propEOpAnd :: Bool -> Bool -> Bool
propEOpAnd n m = bool (eval (eOp oAnd [(eBool n),(eBool m)])) == Just (n && m)

propEOpOr :: Bool -> Bool -> Bool
propEOpOr n m = bool (eval (eOp oOr [(eBool n),(eBool m)])) == Just (n || m)

propEOpImp :: Bool -> Bool -> Bool
propEOpImp n m = bool (eval (eOp oImp [(eBool n),(eBool m)])) == Just (not n || m)

propEOpNot :: Bool -> Bool
propEOpNot n = bool (eval (eOp oNot [(eBool n)])) == Just (not n)

propEOpLe :: Integer -> Integer -> Bool
propEOpLe n m = bool (eval (eOp oLe [(eNum n), (eNum m)])) == Just (n <= m)

propEOpEq :: Integer -> Integer -> Bool
propEOpEq n m = bool (eval (eOp oEq [(eNum n), (eNum m)])) == Just (n == m)

propEIfZero :: Integer -> Integer -> Bool
propEIfZero n m = num (eval (eIf (eNum 0) (eNum n) (eNum m))) == Just n

propEIfNZero :: Integer -> Integer -> Integer -> Bool
propEIfNZero nz n m = if nz == 0 then True else
    num (eval (eIf (eNum nz) (eNum n) (eNum m))) == Just m

propEApp :: Integer -> String -> Bool
propEApp n s = s == "" || 
    num (eval 
            (eApp 
                (eLam s (eOp oMul [(eVar s),(eVar s)]))
                (eNum n))) == Just (n * n)

propERec :: Integer -> String -> String -> Bool
propERec m f n  = f == "" || n == "" || f == n || m < 0 ||
    num (eval (eApp (eFac f n) (eNum m))) == Just (product [1..m])

propEZero :: Bool
propEZero = toInt (eval eZero) == Just 0

propESuc :: Integer -> Bool
propESuc n = n < 0 || toInt (eval (eSuc (eNat n))) == Just (n + 1)

propENat :: Integer -> Bool
propENat n = n < 0 || toInt (eval (eNat n)) == Just n

propECaseZero :: Integer -> Integer -> String -> Bool
propECaseZero n m x = num (eval (eCase eZero (eNum n) x (eNum m))) == Just n

propECaseSuc :: Integer -> Integer -> String -> Bool
propECaseSuc n m x = m <= 0 || 
    toInt (eval (eCase (eNat m) (eNum n) x (eVar x))) == Just (m - 1)

propSum1 :: String -> String -> Integer -> Integer -> Bool
propSum1 x y n m = x == "" || y == "" || x /= y ||  
    num (eval (eApp (eApp (eSum x y) (eNum n)) (eNum m))) == Just (n + m)

propSum2 :: String -> Integer -> Integer -> Bool
propSum2 x n m = x == "" || 
    num (eval (eApp (eApp (eSum x x) (eNum n)) (eNum m))) == Just (m + m)
