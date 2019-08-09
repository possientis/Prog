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
              ]

testValidVar :: Spec
testValidVar = it "Checked valid var property" $
    property $ propValidVar


propValidVar :: (Var -> Var) -> Var -> Bool
propValidVar f x = valid f (Var x) 
