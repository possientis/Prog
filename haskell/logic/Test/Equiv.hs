module  Test.Equiv
    (   specEquiv
    )   where


import Test.Hspec
import Test.QuickCheck  hiding ((===))

import Equiv
import Variable (Var)

specEquiv :: Spec
specEquiv = describe "Testing properties of Equiv..." $ do
    testEquivRefl
    testEquivSym
    testEquivTrans
    testEquivNilIsNil
    
testEquivRefl :: Spec
testEquivRefl = it "Checked reflexivity of Equiv" $ do
    property $ propEquivRefl

testEquivSym :: Spec
testEquivSym = it "Checked symmetry of Equiv" $ do
    property $ propEquivSym

testEquivTrans :: Spec
testEquivTrans = it "Checked transitivity of Equiv" $ do
    property $ propEquivTrans


testEquivNilIsNil :: Spec
testEquivNilIsNil = it "Checked NilIsNil property of Equiv" $ do
    property $ propEquivNilIsNil


propEquivRefl :: [Var] -> Bool
propEquivRefl xs = xs === xs 

propEquivSym :: [Var] -> [Var] -> Bool
propEquivSym xs ys = xs /== ys || ys === xs
 
propEquivTrans :: [Var] -> [Var] -> [Var] -> Bool
propEquivTrans xs ys zs = xs /== ys || ys /== zs || xs === zs

propEquivNilIsNil :: [Var] -> Bool
propEquivNilIsNil xs = xs /== [] || xs == [] 



