module  Haskell.Test.Permute
    (   specPermute
    )   where

import  Test.Hspec
import  Test.QuickCheck

import Haskell.Permute
import Haskell.Variable (Var)

specPermute :: Spec
specPermute = describe "Testing properties for permute (<->)..." $
    sequence_ specsPermute

specsPermute :: [Spec]
specsPermute  = [ testNotation
                , testPermuteComp
                ]

 
testNotation :: Spec
testNotation = it "Checked notation (<->) coincide with 'permute'" $
    property $ propNotation

testPermuteComp :: Spec
testPermuteComp = it "Checked composition property of permute (<->)" $
    property $ propPermuteComp


propNotation :: Var -> Var -> Var -> Bool
propNotation x y u = permute x y u == (x <-> y) u

propPermuteComp :: Var -> Var -> Var -> Var -> Var -> Bool
propPermuteComp a b x y u = (f . (x <-> y)) u == ((f x <-> f y) . f) u
    where f = (a <-> b) -- some prototype of injective function


