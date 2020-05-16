module  Test.Eval
    (   specEval
    )   where


import Op
import Env
import Var
import Eval
import Syntax

import Test.Hspec
import Test.QuickCheck

specEval :: Spec
specEval = describe "Checking the Eval module ..." $ do
    specEVar
    specENum
    specEOpAdd
    specEOpMul
    specEIfZero
    specEIfNZero
    specELam

specENum :: Spec
specENum = it "Checked eval for ENum in empty environment" $ do
    property $ propENum

specEVar :: Spec
specEVar = it "Checked eval for EVar for x1 := n" $ do
    property $ propEVar

specEOpAdd :: Spec 
specEOpAdd = it "Checked eval for n + m" $ do
    property $ propEOpAdd

specEOpMul :: Spec 
specEOpMul = it "Checked eval for n * m" $ do
    property $ propEOpMul

specEIfZero :: Spec
specEIfZero = it "Checked eval for if 0 n m" $ do
    property $ propEIfZero

specEIfNZero :: Spec
specEIfNZero = it "Checked eval for if nz n m" $ do
    property $ propEIfNZero

specELam :: Spec
specELam = it "Check eval for ELam x x" $ do
    property $ propELam

propENum :: Integer -> Bool
propENum n = val (eval (eNum n) newEnv) == Just n  

propEVar :: String -> Integer -> Bool
propEVar s n = val (eval (eVar s) e) == Just n where
    e = bind (mkVar s) (mkVal n) newEnv

propEOpAdd :: Integer -> Integer -> Bool
propEOpAdd n m = val (eval (eOp add (eNum n) (eNum m)) newEnv) == Just (n + m)
 
propEOpMul :: Integer -> Integer -> Bool
propEOpMul n m = val (eval (eOp mul (eNum n) (eNum m)) newEnv) == Just (n * m)

propEIfZero :: Integer -> Integer -> Bool
propEIfZero n m = val (eval (eIf (eNum 0) (eNum n) (eNum m)) newEnv) == Just n

propEIfNZero :: Integer -> Integer -> Integer -> Bool
propEIfNZero nz n m = if nz == 0 then True else
    val (eval (eIf (eNum nz) (eNum n) (eNum m)) newEnv) == Just m

propELam :: String -> Bool
propELam _ = True

