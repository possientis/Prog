module  Test.Difference
    (   specDifference
    )   where

import Test.Hspec
import Test.QuickCheck

import Include
import Intersect
import Difference

import Variable (Var)

specDifference :: Spec
specDifference = describe "Testing properties of difference..." $ do
    testDiffCharac
    testDiffInterComm
    testDiffDistribAppR
    testDiffDistribAppL1
    testDiffDistribAppL2
    testDiffNil

testDiffCharac :: Spec
testDiffCharac = it "Checked characterization of (\\\\)" $ 
    property $ propDiffCharac

testDiffInterComm :: Spec
testDiffInterComm = it "Checked 'commute' property of (\\\\) v (/\\)" $ do
    property $ propDiffInterComm

testDiffDistribAppR :: Spec
testDiffDistribAppR = it "Checked right-distributivity of (\\\\) over (++)"$ do
    property $ propDiffDistribAppR

testDiffDistribAppL1 :: Spec
testDiffDistribAppL1 = it "Checked left-distributivity of (\\\\) over (++) x 1"$ do
    property $ propDiffDistribAppL1

testDiffDistribAppL2 :: Spec
testDiffDistribAppL2 = it "Checked left-distributivity of (\\\\) over (++) x 2"$ do
    property $ propDiffDistribAppL2

testDiffNil :: Spec
testDiffNil = it "Checked xs \\\\ [] == xs" $ do
    property $ propDiffNil

propDiffCharac :: [Var] -> [Var] -> Var -> Bool
propDiffCharac xs ys z = (z `elem` xs \\ ys) == (z `elem` xs && z `notElem` ys)

propDiffInterComm :: [Var] -> [Var] -> [Var] -> Bool
propDiffInterComm xs ys zs = (xs /\ ys) \\ zs <== (xs \\ zs) /\ ys

propDiffDistribAppR :: [Var] -> [Var] -> [Var] -> Bool
propDiffDistribAppR xs ys zs = (xs ++ ys) \\ zs == (xs \\ zs) ++ (ys \\ zs)

propDiffDistribAppL1 :: [Var] -> [Var] -> [Var] -> Bool
propDiffDistribAppL1 xs ys zs = zs \\ (xs ++ ys) == (zs \\ xs) /\ (zs \\ ys)

propDiffDistribAppL2 :: [Var] -> [Var] -> [Var] -> Bool
propDiffDistribAppL2 xs ys zs = zs \\ (xs ++ ys) == (zs \\ xs) \\ ys

propDiffNil :: [Var] -> Bool
propDiffNil xs = xs \\ [] == xs
