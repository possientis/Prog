module  Test.Reduce
    (   specReduce
    )   where

import DSL
import Reduce

import Prelude          hiding (and, or)
import Test.Hspec
import Test.QuickCheck

specReduce :: Spec
specReduce = describe "Checking the Reduce module ..." $ do
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
specEIfT = it "Checked eval for eIf (True)" $ do
    property propEIfT

specEIfF :: Spec
specEIfF = it "Checked eval for eIf (False)" $ do
    property propEIfF

specEZero :: Spec
specEZero = it "Checked eval for eZero" $ do
    property propEZero

specESuc :: Spec
specESuc = it "Checked eval for eSuc" $ do
    property propESuc

propENum :: Integer -> Bool
propENum n = eval (eNum n) == eNum n

propEBool :: Bool -> Bool
propEBool b = eval (eBool b) == eBool b

propEAdd :: Integer -> Integer -> Bool
propEAdd n m = eval (eAdd (eNum n) (eNum m)) == eNum (n + m)

propEMul :: Integer -> Integer -> Bool
propEMul n m = eval (eMul (eNum n) (eNum m)) == eNum (n * m)

propESub :: Integer -> Integer -> Bool
propESub n m = eval (eSub (eNum n) (eNum m)) == eNum (n - m)

propEDiv :: Integer -> Integer -> Bool
propEDiv n m = m == 0 || eval (eDiv (eNum n) (eNum m)) == eNum (n `div` m)

propEAnd :: Bool -> Bool -> Bool
propEAnd n m = eval (eAnd (eBool n) (eBool m)) == eBool (n && m)

propEOr :: Bool -> Bool -> Bool
propEOr n m = eval (eOr (eBool n) (eBool m)) == eBool (n || m)

propEImp :: Bool -> Bool -> Bool
propEImp n m = eval (eImp (eBool n) (eBool m)) == eBool (not n || m)

propENot :: Bool -> Bool
propENot n = eval (eNot (eBool n)) == eBool (not n)

propELe :: Integer -> Integer -> Bool
propELe n m = eval (eLe (eNum n) (eNum m)) == eBool (n <= m)

propEEq :: Integer -> Integer -> Bool
propEEq n m = eval (eEq (eNum n) (eNum m)) == eBool (n == m)

propEIfT :: Integer -> Integer -> Bool
propEIfT n m = eval (eIf (eBool True) (eNum n) (eNum m)) == eNum n

propEIfF :: Integer -> Integer -> Bool
propEIfF n m = eval (eIf (eBool False) (eNum n) (eNum m)) == eNum m

propEZero :: Bool
propEZero = eval eZero == eZero

propESuc :: Integer -> Bool
propESuc n = eval (eSuc (eNat m)) == eval (eNat (1 + pos m)) where
    m = n `mod` 10
