module  Test.Replace
    (   specReplace
    )   where

import  Test.Hspec
import  Test.QuickCheck

import Replace
import Coincide
import Injective
import Variable (Var)

specReplace :: Spec
specReplace = describe "Testing properties for replace (<-:)..." $ do
    testNotation
    testReplaceId
    testReplaceX
    testReplaceY
    testReplaceNotX
    testReplaceTrans
    testReplaceInj
 
testNotation :: Spec
testNotation = it "Checked notation (<-:) coincide with 'flip replace'" $
    property $ propNotation

testReplaceId ::Spec
testReplaceId = it "Checked (x <-: x) is the identity" $
    property $ propReplaceId

testReplaceX :: Spec
testReplaceX = it "Checked (y <-: x) x == y" $ 
    property $ propReplaceX

testReplaceY :: Spec
testReplaceY = it "Checked (y <-: x) y == y" $ 
    property $ propReplaceY

testReplaceNotX :: Spec
testReplaceNotX = it "Checked (y <-: x) u == u for u /= x" $
    property $ propReplaceNotX

testReplaceTrans :: Spec
testReplaceTrans = it "Checked (z <-: y) . (y <-: x) vs (z <-: x)" $ 
    property $ propReplaceTrans

testReplaceInj :: Spec
testReplaceInj = it "Checked replace injective property" $ 
    property $ propReplaceInj

propNotation :: Var -> Var -> Var -> Bool
propNotation x y u = replace x y u == (y <-: x) u

propReplaceId :: Var -> Var -> Bool
propReplaceId x u = (x <-: x) u == u

propReplaceX :: Var -> Var -> Bool
propReplaceX x y = (y <-: x) x == y

propReplaceY :: Var -> Var -> Bool
propReplaceY x y = (y <-: x) y == y

propReplaceNotX :: Var -> Var -> Var -> Bool
propReplaceNotX x y u = (u == x) || (y <-: x) u == u

propReplaceTrans :: Var -> Var -> Var -> [Var] -> Bool
propReplaceTrans x y z ys = (y `elem` ys) || 
    coincide ys ((z <-: y) . (y <-: x)) (z <-: x)

propReplaceInj :: Var -> Var -> [Var] -> Bool
propReplaceInj x y ys = y `elem` ys ||
    injective_on ys (y <-: x)
