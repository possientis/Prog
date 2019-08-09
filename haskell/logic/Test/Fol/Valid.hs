module  Test.Fol.Valid
    (   specValid
    )   where


import Test.Hspec
import Test.QuickCheck

import Variable (Var)
import Formula
import Fol.P

specValid :: Spec
specValid = describe "Testing non-polymorphic properties of valid..." $
    sequence_ specsValid

specsValid :: [Spec]
specsValid  = [ testValidElem
              , testValidBot
              ]

testValidElem :: Spec
testValidElem = it "Checked valid elem property" $
    property $ propValidElem

testValidBot :: Spec
testValidBot = it "Checked valid bot property" $
    property $ propValidBot

propValidElem :: (Var -> Var) -> Var -> Var -> Bool
propValidElem f x y = valid f (Elem x y)


propValidBot :: (Var -> Var) -> Bool
propValidBot f = valid f Bot
