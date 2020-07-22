module  Test.Eval
    (   specEval
    )   where

import DSL
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
    specEIfT
    specEIfF
    specEZero
    specESuc
    specECaseZ
    specECaseS
    specEFac
    specEToNat
    specEFromNat
    specEAddNat
    specEMulNat

pos :: Integer -> Integer 
pos n = if n <= 0 then 0 else n

specENum :: Spec
specENum = it "Checked eval for eNum" $ do
    property propENum

specEBool :: Spec
specEBool = it "Checked eval for eBool" $ do
    property propEBool

specEAdd :: Spec 
specEAdd = it "Checked eval for eAdd" $ do
    property propEAdd

specEMul :: Spec 
specEMul = it "Checked eval for eMul" $ do
    property propEMul

specESub :: Spec 
specESub = it "Checked eval for eSub" $ do
    property propESub

specEDiv :: Spec 
specEDiv = it "Checked eval for eDiv" $ do
    property propEDiv

specEAnd :: Spec 
specEAnd = it "Checked eval for eAnd" $ do
    property propEAnd

specEOr :: Spec 
specEOr = it "Checked eval for eOr" $ do
    property propEOr

specEImp :: Spec 
specEImp = it "Checked eval for eImp" $ do
    property propEImp

specENot :: Spec 
specENot = it "Checked eval for eNot" $ do
    property propENot

specELe :: Spec 
specELe = it "Checked eval for eLe" $ do
    property propELe

specEEq :: Spec 
specEEq = it "Checked eval for eEq" $ do
    property propEEq

specEIfT :: Spec
specEIfT = it "Checked eval for eIf (zero)" $ do
    property propEIfT

specEIfF :: Spec
specEIfF = it "Checked eval for eIf (not zero)" $ do
    property propEIfF

specEZero :: Spec
specEZero = it "Checked eval for eZero" $ do
    property propEZero

specESuc :: Spec
specESuc = it "Checked eval for eSuc" $ do
    property propESuc

specECaseZ :: Spec
specECaseZ = it "Checked eval for eCase (zero)" $ do   
    property propECaseZ

specECaseS :: Spec
specECaseS = it "Checked eval for eCase (successor)" $ do   
    property propECaseS

specEFac :: Spec
specEFac = it "Checked eval for eFac" $ do
    property propEFac

specEToNat :: Spec
specEToNat = it "Checked eval for eToNat" $ do
    property propEToNat

specEFromNat :: Spec
specEFromNat = it "Checked eval for eFromNat" $ do
    property propEFromNat

specEAddNat :: Spec
specEAddNat = it "Checked eval for eAddNat" $ do
    property propEAddNat

specEMulNat :: Spec
specEMulNat = it "Checked eval for eMulNat" $ do
    property propEMulNat

propENum :: Integer -> Bool
propENum n = num (eval (eNum n)) == Just n  

propEBool :: Bool -> Bool
propEBool b = bool (eval (eBool b)) == Just b 

propEAdd :: Integer -> Integer -> Bool
propEAdd n m = num (eval (eApp2 eAdd (eNum n) (eNum m))) == Just (n + m)
 
propEMul :: Integer -> Integer -> Bool
propEMul n m = num (eval (eApp2 eMul (eNum n) (eNum m))) == Just (n * m)

propESub :: Integer -> Integer -> Bool
propESub n m = num (eval (eApp2 eSub (eNum n) (eNum m))) == Just (n - m)

propEDiv :: Integer -> Integer -> Bool
propEDiv n m = m == 0 || 
    num (eval (eApp2 eDiv (eNum n) (eNum m))) == Just (n `div` m)

propEAnd :: Bool -> Bool -> Bool
propEAnd n m = bool (eval (eApp2 eAnd (eBool n) (eBool m))) == Just (n && m)

propEOr :: Bool -> Bool -> Bool
propEOr n m = bool (eval (eApp2 eOr (eBool n) (eBool m))) == Just (n || m)

propEImp :: Bool -> Bool -> Bool
propEImp n m = bool (eval (eApp2 eImp (eBool n) (eBool m))) == Just (not n || m)

propENot :: Bool -> Bool
propENot n = bool (eval (eApp eNot (eBool n))) == Just (not n)

propELe :: Integer -> Integer -> Bool
propELe n m = bool (eval (eApp2 eLe (eNum n) (eNum m))) == Just (n <= m)

propEEq :: Integer -> Integer -> Bool
propEEq n m = bool (eval (eApp2 eEq (eNum n) (eNum m))) == Just (n == m)

propEIfT :: Integer -> Integer -> Bool
propEIfT n m = num (eval (eIf (eBool True) (eNum n) (eNum m))) == Just n

propEIfF :: Integer -> Integer -> Bool
propEIfF n m = num (eval (eIf (eBool False) (eNum n) (eNum m))) == Just m

propEZero :: Bool
propEZero = toInt (eval eZero) == Just 0

propESuc :: Integer -> Bool
propESuc n = toInt (eval (eSuc (eNat n))) == Just (1 + pos n)

propECaseZ :: Integer -> Integer -> String -> Bool
propECaseZ n m x = num (eval (eCase eZero (eNum n) x (eNum m))) == Just n

propECaseS :: Integer -> Integer -> String -> Bool
propECaseS n m x = m <= 0 || 
    toInt (eval (eCase (eNat m) (eNum n) x (eVar x))) == Just (m - 1)

propEFac :: Integer -> Bool
propEFac n  = num (eval (eApp eFac (eNum n))) == Just 
    (if (n <= 0) then 1 else product [1..n])

propEToNat :: Integer -> Bool
propEToNat n = toInt (eval (eApp eToNat (eNum n))) == Just (pos n)

propEFromNat :: Integer -> Bool
propEFromNat n = num (eval (eApp eFromNat (eNat n))) == Just (pos n)

propEAddNat :: Integer -> Integer -> Bool
propEAddNat n m = toInt (eval (eApp2 eAddNat (eNat n) (eNat m))) == Just 
    (pos n + pos m)

propEMulNat :: Integer -> Integer -> Bool
propEMulNat n m = toInt (eval (eApp2 eMulNat (eNat $ n `mod` cap) (eNat $ m `mod` cap))) == Just 
    (pos (n `mod` cap) * pos (m `mod` cap)) where cap = 12 -- too slow otherwise
