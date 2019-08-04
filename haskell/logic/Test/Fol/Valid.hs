module  Test.Fol.Valid
    (   specValid
    )   where


import Test.Hspec
import Test.QuickCheck

import Variable (Var)

import Fol.P
import Fol.Valid
import Fol.Subformula

specValid :: Spec
specValid = describe "Testing properties of valid..." $ 
    sequence_ specsValid

specsValid :: [Spec]
specsValid  = [ testValidSub
              ]

testValidSub :: Spec
testValidSub = it "Checked valid subformula property" $
    property $ propValidSub

propValidSub :: (Var -> Var) -> P Var -> Bool
propValidSub f q = valid f q == all (valid f) (sub q)

