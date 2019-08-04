module  Test.Lam.Valid
    (   specValid
    )   where


import Test.Hspec
import Test.QuickCheck

import Variable (Var)

import Lam.T
import Lam.Valid
import Lam.Subformula

specValid :: Spec
specValid = describe "Testing properties of valid..." $ 
    sequence_ specsValid

specsValid :: [Spec]
specsValid  = [ testValidSub
              ]

testValidSub :: Spec
testValidSub = it "Checked valid subformula property" $
    property $ propValidSub

propValidSub :: (Var -> Var) -> T Var -> Bool
propValidSub f t = valid f t == all (valid f) (sub t)

