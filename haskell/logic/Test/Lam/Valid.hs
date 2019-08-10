module  Test.Lam.Valid
    (   specValid
    )   where


import Test.Hspec
import Test.QuickCheck

import Variable (Var)
import Formula
import Lam.T

specValid :: Spec
specValid = describe "Testing non-polymorphic properties of valid..." $
    sequence_ specsValid

specsValid :: [Spec]
specsValid  = [ testValidVar
              , testValidApp
              ]

testValidVar :: Spec
testValidVar = it "Checked valid var property" $
    property $ propValidVar

testValidApp :: Spec
testValidApp = it "Checked valid app property" $ 
    property $ propValidApp

propValidVar :: (Var -> Var) -> Var -> Bool
propValidVar f x = valid f (Var x) 

propValidApp :: (Var -> Var) -> T Var -> T Var -> Bool
propValidApp f t1 t2 = valid f (App t1 t2) == (valid f t1 && valid f t2)
