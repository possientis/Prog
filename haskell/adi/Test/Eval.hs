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
    specENat
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
    specEIfZ
    specEIfNZ
    specEFac
    specEZero
    specESuc
    specECaseZ
    specECaseS

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

specEIfZ :: Spec
specEIfZ = it "Checked eval for eIf (zero)" $ do
    property $ propEIfZ

specEIfNZ :: Spec
specEIfNZ = it "Checked eval for eIf (not zero)" $ do
    property $ propEIfNZ

specEFac :: Spec
specEFac = it "Checked eval for eFac" $ do
    property $ propEFac

specEZero :: Spec
specEZero = it "Checked eval for eZero" $ do
    property $ propEZero

specESuc :: Spec
specESuc = it "Checked eval for eSuc" $ do
    property $ propESuc

specECaseZ :: Spec
specECaseZ = it "Checked eval for eCase (zero)" $ do   
    property $ propECaseZ

specECaseS :: Spec
specECaseS = it "Checked eval for eCase (successor)" $ do   
    property $ propECaseS

propENum :: Integer -> Bool
propENum n = num (eval (eNum n)) == Just n  

propEBool :: Bool -> Bool
propEBool b = bool (eval (eBool b)) == Just b 

propENat :: Integer -> Bool
propENat n = n < 0 || toInt (eval (eNat n)) == Just n

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

propEIfZ :: Integer -> Integer -> Bool
propEIfZ n m = num (eval (eIf (eNum 0) (eNum n) (eNum m))) == Just n

propEIfNZ :: Integer -> Integer -> Integer -> Bool
propEIfNZ nz n m = if nz == 0 then True else
    num (eval (eIf (eNum nz) (eNum n) (eNum m))) == Just m

propEFac :: Integer -> String -> String -> Bool
propEFac m f n  = f == "" || n == "" || f == n || m < 0 ||
    num (eval (eApp eFac (eNum m))) == Just (product [1..m])

propEZero :: Bool
propEZero = toInt (eval eZero) == Just 0

propESuc :: Integer -> Bool
propESuc n = n < 0 || toInt (eval (eSuc (eNat n))) == Just (n + 1)

propECaseZ :: Integer -> Integer -> String -> Bool
propECaseZ n m x = num (eval (eCase eZero (eNum n) x (eNum m))) == Just n

propECaseS :: Integer -> Integer -> String -> Bool
propECaseS n m x = m <= 0 || 
    toInt (eval (eCase (eNat m) (eNum n) x (eVar x))) == Just (m - 1)
