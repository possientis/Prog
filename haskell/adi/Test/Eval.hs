{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}

module  Test.Eval
    (   specEval   
    )   where

import DSL
import Eval
import Value

import Prelude          hiding (and, or)
import Test.Hspec
import Test.QuickCheck

specEval :: forall m . (Eval m) => Spec
specEval = describe "Checking the Eval module ..." $ do
    specENum        @ m
    specEBool       @ m
    specEAdd        @ m
    specEMul        @ m
    specESub        @ m
    specEDiv        @ m
    specEAnd        @ m
    specEOr         @ m
    specEImp        @ m
    specENot        @ m
    specELe         @ m
    specEEq         @ m
    specEIfT        @ m
    specEIfF        @ m
    specEZero       @ m
    specESuc        @ m
    specECaseZ      @ m
    specECaseS      @ m
    specEFac        @ m
    specEToNat      @ m
    specEFromNat    @ m
    specEAddNat     @ m
    specEMulNat     @ m

pos :: Integer -> Integer 
pos n = if n <= 0 then 0 else n

specENum :: forall m . (Eval m) => Spec
specENum = it "Checked eval for eNum" $ do
    property (propENum @ m)

specEBool :: forall m . (Eval m) =>  Spec
specEBool = it "Checked eval for eBool" $ do
    property (propEBool @ m)

specEAdd :: forall m . (Eval m) =>  Spec 
specEAdd = it "Checked eval for eAdd" $ do
    property (propEAdd @ m)

specEMul :: forall m . (Eval m) =>  Spec 
specEMul = it "Checked eval for eMul" $ do
    property (propEMul @ m)

specESub :: forall m . (Eval m) =>  Spec 
specESub = it "Checked eval for eSub" $ do
    property (propESub @ m)

specEDiv :: forall m . (Eval m) =>  Spec 
specEDiv = it "Checked eval for eDiv" $ do
    property (propEDiv @ m)

specEAnd :: forall m . (Eval m) =>  Spec 
specEAnd = it "Checked eval for eAnd" $ do
    property (propEAnd @ m)

specEOr :: forall m . (Eval m) =>  Spec 
specEOr = it "Checked eval for eOr" $ do
    property (propEOr @ m)

specEImp :: forall m . (Eval m) =>  Spec 
specEImp = it "Checked eval for eImp" $ do
    property (propEImp @ m)

specENot :: forall m . (Eval m) =>  Spec 
specENot = it "Checked eval for eNot" $ do
    property (propENot @ m)

specELe :: forall m . (Eval m) =>  Spec 
specELe = it "Checked eval for eLe" $ do
    property (propELe @ m)

specEEq :: forall m . (Eval m) =>  Spec 
specEEq = it "Checked eval for eEq" $ do
    property (propEEq @ m)

specEIfT :: forall m . (Eval m) =>  Spec
specEIfT = it "Checked eval for eIf (True)" $ do
    property (propEIfT @ m)

specEIfF :: forall m . (Eval m) =>  Spec
specEIfF = it "Checked eval for eIf (False)" $ do
    property (propEIfF @ m)

specEZero :: forall m . (Eval m) =>  Spec
specEZero = it "Checked eval for eZero" $ do
    property (propEZero @ m)

specESuc :: forall m . (Eval m) =>  Spec
specESuc = it "Checked eval for eSuc" $ do
    property (propESuc @ m)

specECaseZ :: forall m . (Eval m) =>  Spec
specECaseZ = it "Checked eval for eCase (zero)" $ do   
    property (propECaseZ @ m)

specECaseS :: forall m . (Eval m) =>  Spec
specECaseS = it "Checked eval for eCase (suc)" $ do   
    property (propECaseS @ m)

specEFac :: forall m . (Eval m) =>  Spec
specEFac = it "Checked eval for eFac" $ do
    property (propEFac @ m)

specEToNat :: forall m . (Eval m) =>  Spec
specEToNat = it "Checked eval for eToNat" $ do
    property (propEToNat @ m)

specEFromNat :: forall m . (Eval m) =>  Spec
specEFromNat = it "Checked eval for eFromNat" $ do
    property (propEFromNat @ m)

specEAddNat :: forall m . (Eval m) =>  Spec
specEAddNat = it "Checked eval for eAddNat" $ do
    property (propEAddNat @ m)

specEMulNat :: forall m . (Eval m) =>  Spec
specEMulNat = it "Checked eval for eMulNat" $ do
    property (propEMulNat @ m)

propENum :: forall m . (Eval m) => Integer -> Bool
propENum n = num ((eval @ m) (eNum n)) == Just n  

propEBool :: forall m . (Eval m) => Bool -> Bool
propEBool b = bool ((eval @ m) (eBool b)) == Just b 

propEAdd :: forall m . (Eval m) => Integer -> Integer -> Bool
propEAdd n m = num ((eval @ m) (eAdd (eNum n) (eNum m))) == Just (n + m)
 
propEMul :: forall m . (Eval m) => Integer -> Integer -> Bool
propEMul n m = num ((eval @ m) (eMul (eNum n) (eNum m))) == Just (n * m)

propESub :: forall m . (Eval m) => Integer -> Integer -> Bool
propESub n m = num ((eval @ m) (eSub (eNum n) (eNum m))) == Just (n - m)

propEDiv :: forall m . (Eval m) => Integer -> Integer -> Bool
propEDiv n m = m == 0 || 
    num ((eval @ m) (eDiv (eNum n) (eNum m))) == Just (n `div` m)

propEAnd :: forall m . (Eval m) => Bool -> Bool -> Bool
propEAnd n m = bool ((eval @ m) (eAnd (eBool n) (eBool m))) == Just (n && m)

propEOr :: forall m . (Eval m) => Bool -> Bool -> Bool
propEOr n m = bool ((eval @ m) (eOr (eBool n) (eBool m))) == Just (n || m)

propEImp :: forall m . (Eval m) => Bool -> Bool -> Bool
propEImp n m = bool ((eval @ m) (eImp (eBool n) (eBool m))) == Just (not n || m)

propENot :: forall m . (Eval m) => Bool -> Bool
propENot n = bool ((eval @ m) (eNot (eBool n))) == Just (not n)

propELe :: forall m . (Eval m) => Integer -> Integer -> Bool
propELe n m = bool ((eval @ m) (eLe (eNum n) (eNum m))) == Just (n <= m)

propEEq :: forall m . (Eval m) => Integer -> Integer -> Bool
propEEq n m = bool ((eval @ m) (eEq (eNum n) (eNum m))) == Just (n == m)

propEIfT :: forall m . (Eval m) => Integer -> Integer -> Bool
propEIfT n m = num ((eval @ m) (eIf (eBool True) (eNum n) (eNum m))) == Just n

propEIfF :: forall m . (Eval m) => Integer -> Integer -> Bool
propEIfF n m = num ((eval @ m) (eIf (eBool False) (eNum n) (eNum m))) == Just m

propEZero :: forall m . (Eval m) => Bool
propEZero = toInt ((eval @ m) eZero) == Just 0

propESuc :: forall m . (Eval m) => Integer -> Bool
propESuc n = toInt ((eval @ m) (eSuc (eNat n'))) == Just (1 + pos n')
    where n' = n `mod` cap

propECaseZ :: forall m . (Eval m) => Integer -> String -> Bool
propECaseZ n x = num ((eval @ m) (eCase eZero (eNum n) x (eVar x))) == Just n

propECaseS :: forall m . (Eval m) => Integer -> Integer -> String -> Bool
propECaseS n m x = m' <= 0 || x == "" ||
    toInt ((eval @ m) (eCase (eNat m') (eNum n) x (eVar x))) == Just (m' - 1)
    where m' = m `mod` cap

propEFac :: forall m . (Eval m) => Integer -> Bool
propEFac n  = num ((eval @ m) (eApp eFac (eNum n))) == Just 
    (if (n <= 0) then 1 else product [1..n])

propEToNat :: forall m . (Eval m) => Integer -> Bool
propEToNat n = toInt ((eval @ m) (eApp eToNat (eNum n'))) == Just (pos n')
    where n' = n `mod` cap

propEFromNat :: forall m . (Eval m) => Integer -> Bool
propEFromNat n = num ((eval @ m) (eApp eFromNat (eNat n'))) == Just (pos n')
    where n' = n `mod` cap

propEAddNat :: forall m. (Eval m) => Integer -> Integer -> Bool
propEAddNat n m = toInt ((eval @ m) (eApp2 eAddNat (eNat n') (eNat m'))) == Just 
    (pos n' + pos m')
    where -- to slow otherwise 
        n' = n `mod` cap
        m' = m `mod` cap

propEMulNat :: forall m . (Eval m) => Integer -> Integer -> Bool
propEMulNat n m = toInt ((eval @ m) (eApp2 eMulNat (eNat n') (eNat m'))) == Just 
    (pos n' * pos m') 
    where -- to slow otherwise 
        n' = n `mod` cap
        m' = m `mod` cap

cap :: Integer
cap = 7
