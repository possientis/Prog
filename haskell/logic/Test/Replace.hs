module  Test.Replace
    (   specReplace
    )   where

import  Test.Hspec
import  Test.QuickCheck

import Replace
import Coincide
import Variable (Var)

specReplace :: Spec
specReplace = describe "Testing properties for replace (<-:)..." $
    sequence_ specsReplace

specsReplace :: [Spec]
specsReplace  = [ testNotation
                , testReplaceId
                , testReplace_x
                , testReplace_y
                , testReplace_not_x
                , testReplace_trans
                ]

 
testNotation :: Spec
testNotation = it "Checked notation (<-:) coincide with 'flip replace'" $
    property $ propNotation

testReplaceId ::Spec
testReplaceId = it "Checked (x <-: x) is the identity" $
    property $ propReplaceId

testReplace_x :: Spec
testReplace_x = it "Checked (y <-: x) x == y" $ 
    property $ propReplace_x

testReplace_y :: Spec
testReplace_y = it "Checked (y <-: x) y == y" $ 
    property $ propReplace_y

testReplace_not_x :: Spec
testReplace_not_x = it "Checked (y <-: x) u == u for u /= x" $
    property $ propReplace_not_x

testReplace_trans :: Spec
testReplace_trans = it "Checked (z <-: y) . (y <-: x) vs (z <-: x)" $ 
    property $ propReplace_trans

propNotation :: Var -> Var -> Var -> Bool
propNotation x y u = replace x y u == (y <-: x) u

propReplaceId :: Var -> Var -> Bool
propReplaceId x u = (x <-: x) u == u

propReplace_x :: Var -> Var -> Bool
propReplace_x x y = (y <-: x) x == y

propReplace_y :: Var -> Var -> Bool
propReplace_y x y = (y <-: x) y == y

propReplace_not_x :: Var -> Var -> Var -> Bool
propReplace_not_x x y u = (u == x) || (y <-: x) u == u

propReplace_trans :: Var -> Var -> Var -> [Var] -> Bool
propReplace_trans x y z ys = (y `elem` ys) || 
    coincide ys ((z <-: y) . (y <-: x)) (z <-: x)


