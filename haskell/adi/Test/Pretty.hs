module  Test.Pretty
    (   specPretty
    )   where

import DSL
import Pretty

import Test.Hspec
import Test.QuickCheck


specPretty :: Spec
specPretty = describe "Checking the Pretty module..." $ do
    specENum
    specEBool
    specEAdd

specENum :: Spec
specENum = it "Checked showExpr for eNum" $ 
    property propENum

specEBool :: Spec
specEBool = it "Checked showExpr for eBool" $ 
    property propEBool

specEAdd :: Spec
specEAdd = it "Checked showExpr for eAdd" $
    property propEAdd

propENum :: Integer -> Bool
propENum n = showExpr (eNum n) == show n

propEBool :: Bool -> Bool
propEBool b = showExpr (eBool b) == show b

propEAdd :: Integer -> Integer -> Bool
propEAdd n m = showExpr (eAdd (eNum n) (eNum m)) == show n ++ " + " ++ show m
