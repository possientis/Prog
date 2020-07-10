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
    testEquivConsCompat
    testEquivCompatLR
    
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

testEquivConsCompat :: Spec
testEquivConsCompat = it "Checked the equiv compatibility of cons" $ do
    property $ propEquivConsCompat

testEquivCompatLR :: Spec
testEquivCompatLR = it "Checked the left-right equiv compatibility of equiv" $ do
    property $ propEquivCompatLR

propEquivRefl :: [Var] -> Bool
propEquivRefl xs = xs === xs 

propEquivSym :: [Var] -> [Var] -> Bool
propEquivSym xs ys = xs /== ys || ys === xs
 
propEquivTrans :: [Var] -> [Var] -> [Var] -> Bool
propEquivTrans xs ys zs = xs /== ys || ys /== zs || xs === zs

propEquivNilIsNil :: [Var] -> Bool
propEquivNilIsNil xs = xs /== [] || xs == [] 

propEquivConsCompat :: Var -> [Var] -> [Var] -> Bool
propEquivConsCompat x xs ys = xs /== ys || (x : xs) === (x : ys)

propEquivCompatLR :: [Var] -> [Var] -> [Var] -> [Var] -> Bool
propEquivCompatLR xs' ys' xs ys = xs /== xs' || ys /== ys' || xs === ys

