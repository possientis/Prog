module  Test.Func.Permute
    (   specPermute
    )   where

import  Test.Hspec
import  Test.QuickCheck

import List.Coincide
import Variable (Var)

import Func.Replace
import Func.Permute

specPermute :: Spec
specPermute = describe "Testing properties for permute (<->)..." $ do
    testNotation
    testPermuteComp
    testPermuteReplace
 
testNotation :: Spec
testNotation = it "Checked notation (<->) coincide with 'permute'" $
    property $ propNotation

testPermuteComp :: Spec
testPermuteComp = it "Checked composition property of permute (<->)" $
    property $ propPermuteComp

testPermuteReplace :: Spec
testPermuteReplace = it "Checked when (y <-: x) and (x <-> y) coincide" $
    property $ propPermuteReplace


propNotation :: Var -> Var -> Var -> Bool
propNotation x y u = permute x y u == (x <-> y) u

propPermuteComp :: Var -> Var -> Var -> Var -> Var -> Bool
propPermuteComp a b x y u = (f . (x <-> y)) u == ((f x <-> f y) . f) u
    where f = (a <-> b) -- some prototype of injective function

propPermuteReplace :: Var -> Var -> [Var] -> Bool
propPermuteReplace x y xs = y `elem` xs || coincide xs (y <-: x) (x <-> y) 


