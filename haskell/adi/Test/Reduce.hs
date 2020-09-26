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

specENum :: Spec
specENum = it "Checked eval for eNum" $ do
    property propENum

specEBool :: Spec
specEBool = it "Checked eval for eBool" $ do
    property propEBool

specEAdd :: Spec
specEAdd = it "Checked eval for eAdd" $ do
    property propEAdd


propENum :: Integer -> Bool
propENum n = eval (eNum n) == eNum n

propEBool :: Bool -> Bool
propEBool b = eval (eBool b) == eBool b

propEAdd :: Integer -> Integer -> Bool
propEAdd n m = eval (eAdd (eNum n) (eNum m)) == eNum (n + m)
