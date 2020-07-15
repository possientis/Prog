module  Test.Eval
    (   specEval
    )   where

import DSL
import Macro    -- remove
import Value
import Interpret

import Prelude          hiding (and, or)
import Test.Hspec
import Test.QuickCheck

specEval :: Spec
specEval = describe "Checking the Eval module ..." $ do
    specENum
    specEBool
    specEAdd
    specEMul
    specESub
    specEDiv
    specEAnd
    specEOr
    specEImp
    specENot
    specELe
    specEEq
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

specENat :: Spec
specENat = it "Checked eval for eNat" $ do
    property $ propENat

specEAdd :: Spec 
specEAdd = it "Checked eval for eAdd" $ do
    property $ propEAdd

specEMul :: Spec 
specEMul = it "Checked eval for eMul" $ do
    property $ propEMul

specESub :: Spec 
specESub = it "Checked eval for eSub" $ do
    property $ propESub

specEDiv :: Spec 
specEDiv = it "Checked eval for eDiv" $ do
    property $ propEDiv

specEAnd :: Spec 
specEAnd = it "Checked eval for eAnd" $ do
    property $ propEAnd

specEOr :: Spec 
specEOr = it "Checked eval for eOr" $ do
    property $ propEOr

specEImp :: Spec 
specEImp = it "Checked eval for eImp" $ do
    property $ propEImp

specENot :: Spec 
specENot = it "Checked eval for eNot" $ do
    property $ propENot

specELe :: Spec 
specELe = it "Checked eval for eLe" $ do
    property $ propELe

specEEq :: Spec 
specEEq = it "Checked eval for eEq" $ do
    property $ propEEq

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

propENat :: Integer -> Bool
propENat n = n < 0 || toInt (eval (eNat n)) == Just n

propEAdd :: Integer -> Integer -> Bool
propEAdd n m = num (eval (eAdd (eNum n) (eNum m))) == Just (n + m)
 
propEMul :: Integer -> Integer -> Bool
propEMul n m = num (eval (eMul (eNum n) (eNum m))) == Just (n * m)

propESub :: Integer -> Integer -> Bool
propESub n m = num (eval (eSub (eNum n) (eNum m))) == Just (n - m)

propEDiv :: Integer -> Integer -> Bool
propEDiv n m = m == 0 || 
    num (eval (eDiv (eNum n) (eNum m))) == Just (n `div` m)

propEAnd :: Bool -> Bool -> Bool
propEAnd n m = bool (eval (eAnd (eBool n) (eBool m))) == Just (n && m)

propEOr :: Bool -> Bool -> Bool
propEOr n m = bool (eval (eOr (eBool n) (eBool m))) == Just (n || m)

propEImp :: Bool -> Bool -> Bool
propEImp n m = bool (eval (eImp (eBool n) (eBool m))) == Just (not n || m)

propENot :: Bool -> Bool
propENot n = bool (eval (eNot (eBool n))) == Just (not n)

propELe :: Integer -> Integer -> Bool
propELe n m = bool (eval (eLe (eNum n) (eNum m))) == Just (n <= m)

propEEq :: Integer -> Integer -> Bool
propEEq n m = bool (eval (eEq (eNum n) (eNum m))) == Just (n == m)

propEIfZero :: Integer -> Integer -> Bool
propEIfZero n m = num (eval (eIf (eNum 0) (eNum n) (eNum m))) == Just n

propEIfNZero :: Integer -> Integer -> Integer -> Bool
propEIfNZero nz n m = if nz == 0 then True else
    num (eval (eIf (eNum nz) (eNum n) (eNum m))) == Just m

propEApp :: Integer -> String -> Bool
propEApp n s = s == "" || 
    num (eval 
            (eApp 
                (eLam s (eMul (eVar s) (eVar s)))
                (eNum n))) == Just (n * n)

propERec :: Integer -> String -> String -> Bool
propERec m f n  = f == "" || n == "" || f == n || m < 0 ||
    num (eval (eApp (eFac f n) (eNum m))) == Just (product [1..m])

propEZero :: Bool
propEZero = toInt (eval eZero) == Just 0

propESuc :: Integer -> Bool
propESuc n = n < 0 || toInt (eval (eSuc (eNat n))) == Just (n + 1)


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
