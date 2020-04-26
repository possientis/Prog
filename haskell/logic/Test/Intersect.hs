module  Test.Intersect
    (   specIntersect
    )   where

import Data.List

import Test.Hspec
import Test.QuickCheck

import Intersect
import Variable (Var)


specIntersect :: Spec
specIntersect = describe "Testing properties of intersect..." $ do
    testInterIntersect
    testInterCharac
    testInterDistribAppR
    testInterConsNotInR
    testInterConsNotInL
    testInterConsInR
    testInterNil

testInterIntersect :: Spec
testInterIntersect = it "Checked inter coincide with GHC 'intersect'" $
    property $ propInterIntersect

testInterCharac :: Spec
testInterCharac = it "Checked inter characterization property" $
    property $ propInterCharac

testInterDistribAppR :: Spec
testInterDistribAppR = it "Checked right-distributivity of (/\\) over (++)" $ do
    property $ propInterDistribAppR

testInterConsNotInR :: Spec
testInterConsNotInR = it "Checked not elem -> xs /\\ (cons y ys) == xs /\\ ys" $ do
    property $ propInterConsNotInR

testInterConsNotInL :: Spec
testInterConsNotInL = it "Checked not elem -> (cons x xs) /\\ ys == xs /\\ ys" $ do
    property $ propInterConsNotInL

testInterConsInR :: Spec
testInterConsInR = it "Checked elem -> xs /\\ (cons y ys) == xs /\\ ys" $ do
    property $ propInterConsInR

testInterNil :: Spec
testInterNil = it "Checked xs /\\ [] == xs" $ do
    property $ propInterNil

propInterIntersect :: [Var] -> [Var] -> Bool
propInterIntersect xs ys = xs /\ ys == intersect xs ys

propInterCharac :: [Var] -> [Var] -> Var -> Bool
propInterCharac xs ys z = (z `elem` xs /\ ys) == (z `elem` xs && z `elem` ys)

propInterDistribAppR :: [Var] -> [Var] -> [Var] -> Bool
propInterDistribAppR xs ys zs = (xs ++ ys) /\ zs == (xs /\ zs) ++ (ys /\ zs)

propInterConsNotInR :: [Var] -> [Var] -> Var -> Bool
propInterConsNotInR xs ys y = y `elem` xs || xs /\ (y : ys) == xs /\ ys

propInterConsNotInL :: [Var] -> [Var] -> Var -> Bool
propInterConsNotInL xs ys x = x `elem` ys || (x : xs) /\ ys == xs /\ ys

propInterConsInR :: [Var] -> [Var] -> Var -> Bool
propInterConsInR xs ys y = y `notElem` ys || xs /\ (y : ys) == xs /\ ys 

propInterNil :: [Var] -> Bool
propInterNil xs = xs /\ [] == []

