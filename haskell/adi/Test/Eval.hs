module  Test.Eval
    (   x1, x2
    ,   specEval
    )   where


import Env
import Eval
import Syntax

import Test.Hspec
import Test.QuickCheck

specEval :: Spec
specEval = describe "Checking the Eval module ..." $ do
    specENum

specENum :: Spec
specENum = it "Checked eval for ENum in empty environment" $ do
    property $ propENum


propENum :: Integer -> Bool
propENum n = val (eval (eNum n) newEnv) == Just n  
 
x1 :: Expr
x1  = eVar "x1"

x2 :: Expr 
x2 = eVar "x2"


 
