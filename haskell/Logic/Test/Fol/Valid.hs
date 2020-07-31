module  Test.Fol.Valid
    (   specValid
    )   where


import Test.Hspec
import Test.QuickCheck

import Variable (Var)
import Formula
import Fol.P

specValid :: Spec
specValid = describe "Testing non-polymorphic properties of valid..." $ do
    testValidElem
    testValidBot
    testValidImp
    testValidAll
    testValidCharac

testValidElem :: Spec
testValidElem = it "Checked valid elem property" $
    property $ propValidElem

testValidBot :: Spec
testValidBot = it "Checked valid bot property" $
    property $ propValidBot

testValidImp :: Spec
testValidImp = it "Checked valid imp property" $ 
    property $ propValidImp

testValidAll :: Spec
testValidAll = it "Checked valid all property" $ 
    property $ propValidAll

testValidCharac :: Spec
testValidCharac = it "Checked valid characterization property" $ 
    property $ propValidCharac

propValidElem :: (Var -> Var) -> Var -> Var -> Bool
propValidElem f x y = valid f (Elem x y)

propValidBot :: (Var -> Var) -> Bool
propValidBot f = valid f Bot

propValidImp :: (Var -> Var) -> P Var -> P Var -> Bool
propValidImp f p1 p2 = valid f (Imp p1 p2) == (valid f p1 && valid f p2)

propValidAll :: (Var -> Var) -> P Var -> Var -> Bool
propValidAll f p1 x = valid f (All x p1) == 
   (valid f p1 && all ((/= f x) . f) (free $ All x p1))

propValidCharac :: (Var -> Var) -> P Var -> Bool
propValidCharac f p = valid f p == all cond (sub p) where
    cond :: P Var -> Bool
    cond p'@(All x _) = all ((/= f x) . f) (free p')
    cond _            = True
