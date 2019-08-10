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
              , testValidImp
              ]

testValidElem :: Spec
testValidElem = it "Checked valid elem property" $
    property $ propValidElem

testValidBot :: Spec
testValidBot = it "Checked valid bot property" $
    property $ propValidBot

testValidImp :: Spec
testValidImp = it "Checked valid imp property" $ 
    property $ propValidImp

propValidElem :: (Var -> Var) -> Var -> Var -> Bool
propValidElem f x y = valid f (Elem x y)

propValidBot :: (Var -> Var) -> Bool
propValidBot f = valid f Bot

propValidImp :: (Var -> Var) -> P Var -> P Var -> Bool
propValidImp f p1 p2 = valid f (Imp p1 p2) == (valid f p1 && valid f p2)
