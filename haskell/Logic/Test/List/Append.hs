module  Test.List.Append
    (   specAppend
    )   where

import List.Equiv
import Variable (Var)

import Test.Hspec
import Test.QuickCheck  hiding ((===))

specAppend :: Spec
specAppend = describe "Testing properties of append..." $ do
    testAppCharac
    testAppCompatL
    testAppCompatR
    testAppCompatLR
    testAppAssoc'
    testAppComm
    testAppNil

testAppCharac :: Spec
testAppCharac = it "Checked characterization of (++)" $ 
    property propAppCharac

testAppCompatL :: Spec
testAppCompatL = it "Checked the left compatibility of (++) with (===)" $ do
    property propAppCompatL

testAppCompatR :: Spec
testAppCompatR = it "Checked the right compatibility of (++) with (===)" $ do
    property propAppCompatR

testAppCompatLR :: Spec
testAppCompatLR = it "Checked the compatibility of (++) with (===)" $ do
    property propAppCompatLR

testAppAssoc' :: Spec
testAppAssoc' = it "Checked the associativity of (++)" $ do
    property propAppAssoc'

testAppComm :: Spec
testAppComm = it "Checked the commutativity of (++)" $ do
    property propAppComm 

testAppNil :: Spec
testAppNil = it "Checked the (++) nil property" $ do
    property propAppNil

propAppCharac :: [Var] -> [Var] -> Var -> Bool
propAppCharac xs ys z = 
    (z `elem` (xs ++ ys)) == (z `elem` xs) || (z `elem` ys)

propAppCompatL :: [Var] -> [Var] -> [Var] -> Bool
propAppCompatL xs xs' ys = xs /== xs' || xs ++ ys === xs' ++ ys

propAppCompatR :: [Var] -> [Var] -> [Var] -> Bool
propAppCompatR xs ys ys' = ys /== ys' || xs ++ ys === xs ++ ys'

propAppCompatLR :: [Var]-> [Var] -> [Var] -> [Var] -> Bool
propAppCompatLR xs xs' ys ys' = ys /== ys' || xs /== xs' || 
    xs ++ ys === xs' ++ ys'

propAppAssoc' :: [Var] -> [Var] -> [Var] -> Bool
propAppAssoc' xs ys zs = (xs ++ ys) ++ zs === xs ++ (ys ++ zs)

propAppComm :: [Var] -> [Var] -> Bool
propAppComm xs ys = xs ++ ys === ys ++ xs

propAppNil :: [Var] -> [Var] -> Bool
propAppNil xs ys = not (xs ++ ys == []) || (xs == [] && ys == [])

