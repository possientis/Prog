module  Test.Append
    (   specAppend
    )   where

import Equiv
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

testAppCharac :: Spec
testAppCharac = it "Checked characterization of (++)" $ 
    property $ propAppCharac

propAppCharac :: [Var] -> [Var] -> Var -> Bool
propAppCharac xs ys z = 
    (z `elem` (xs ++ ys)) == (z `elem` xs) || (z `elem` ys)

testAppCompatL :: Spec
testAppCompatL = it "Checked the left compatibility of (++) with (===)" $ do
    property $ propAppCompatL

testAppCompatR :: Spec
testAppCompatR = it "Checked the right compatibility of (++) with (===)" $ do
    property $ propAppCompatR

testAppCompatLR :: Spec
testAppCompatLR = it "Checked the compatibility of (++) with (===)" $ do
    property $ propAppCompatLR

testAppAssoc' :: Spec
testAppAssoc' = it "Checked the associativity of (++)" $ do
    property $ propAppAssoc'

testAppComm :: Spec
testAppComm = it "Checked the commutativity of (++)" $ do
    property $ propAppComm 

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
