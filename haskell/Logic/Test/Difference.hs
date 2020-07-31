module  Test.Difference
    (   specDifference
    )   where

import Test.Hspec
import Test.QuickCheck  hiding ((===))

import Equiv
import Include
import Intersect
import Difference

import Variable (Var)

specDifference :: Spec
specDifference = describe "Testing properties of difference..." $ do
    testDiffCharac
    testDiffInterComm
    testDiffInterAssoc
    testDiffDistribAppR
    testDiffDistribAppL
    testDiffDistribAppL'
    testDiffNil
    testDiffInclR
    testDiffCompatL
    testDiffCompatR
    testDiffCompatR2
    testDiffCompatR3
    testDiffCompatLR
    testDiffInter
    testDiffNotIn
    testDiffConcat
    testDiffAppend

testDiffCharac :: Spec
testDiffCharac = it "Checked characterization of (\\\\)" $ 
    property $ propDiffCharac

testDiffInterComm :: Spec
testDiffInterComm = it "Checked 'commute' property of (\\\\) v (/\\)" $ do
    property $ propDiffInterComm

testDiffInterAssoc :: Spec
testDiffInterAssoc = it "Checked 'assoc' property of (\\\\) v (/\\)" $ do
    property $ propDiffInterAssoc

testDiffDistribAppR :: Spec
testDiffDistribAppR = it "Checked right-distributivity of (\\\\) over (++)"$ do
    property $ propDiffDistribAppR

testDiffDistribAppL :: Spec
testDiffDistribAppL = it "Checked left-distributivity of (\\\\) over (++) x 1"$ do
    property $ propDiffDistribAppL

testDiffDistribAppL' :: Spec
testDiffDistribAppL' = it "Checked left-distributivity of (\\\\) over (++) x 2"$ do
    property $ propDiffDistribAppL'

testDiffNil :: Spec
testDiffNil = it "Checked xs \\\\ [] == xs" $ do
    property $ propDiffNil

testDiffInclR :: Spec
testDiffInclR = it "Checked the right compatibility of (\\\\) with  (<==)" $ do
    property $ propDiffInclR

testDiffCompatL :: Spec
testDiffCompatL = it "Checked the left compatibility of (\\\\) with (===)" $ do
    property $ propDiffCompatL

testDiffCompatR :: Spec
testDiffCompatR = it "Checked the right compatibility of (\\\\) with (===)" $ do
    property $ propDiffCompatR

testDiffCompatR2 :: Spec
testDiffCompatR2 = it "Checked the right compatibility of (\\\\) with (==)" $ do
    property $ propDiffCompatR2

testDiffCompatR3 :: Spec
testDiffCompatR3 = it "Checked the right compatibility of (\\\\) with (/\\)" $ do
    property $ propDiffCompatR3

testDiffCompatLR :: Spec
testDiffCompatLR = it "Checked the compatibility of (\\\\) with (===)" $ do
    property $ propDiffCompatLR

testDiffInter :: Spec
testDiffInter = it "Checked xs \\\\ ys == xs \\\\ (xs /\\ ys)" $ do
    property $ propDiffInter

testDiffNotIn :: Spec
testDiffNotIn = it "Checked the diff_not_in property" $ do
    property $ propDiffNotIn

testDiffConcat :: Spec
testDiffConcat = it "Checked the diff_concat property" $ do
    property $ propDiffConcat

testDiffAppend :: Spec
testDiffAppend = it "Checked the diff_append property" $ do
    property $ propDiffAppend

propDiffCharac :: [Var] -> [Var] -> Var -> Bool
propDiffCharac xs ys z = (z `elem` xs \\ ys) == (z `elem` xs && z `notElem` ys)

propDiffInterComm :: [Var] -> [Var] -> [Var] -> Bool
propDiffInterComm xs ys zs = (xs /\ ys) \\ zs === (xs \\ zs) /\ ys

propDiffInterAssoc :: [Var] -> [Var] -> [Var] -> Bool
propDiffInterAssoc xs ys zs = (xs /\ ys) \\ zs === xs /\ (ys \\ zs)

propDiffDistribAppR :: [Var] -> [Var] -> [Var] -> Bool
propDiffDistribAppR xs ys zs = (xs ++ ys) \\ zs == (xs \\ zs) ++ (ys \\ zs)

propDiffDistribAppL :: [Var] -> [Var] -> [Var] -> Bool
propDiffDistribAppL xs ys zs = zs \\ (xs ++ ys) == (zs \\ xs) /\ (zs \\ ys)

propDiffDistribAppL' :: [Var] -> [Var] -> [Var] -> Bool
propDiffDistribAppL' xs ys zs = zs \\ (xs ++ ys) == (zs \\ xs) \\ ys

propDiffNil :: [Var] -> Bool
propDiffNil xs = xs \\ [] == xs

propDiffInclR :: [Var] -> [Var] -> [Var] -> Bool
propDiffInclR xs ys zs = not (xs <== ys) || zs \\ ys <== zs \\ xs

propDiffCompatL :: [Var] -> [Var] -> [Var] -> Bool
propDiffCompatL xs xs' ys = xs /== xs' || xs \\ ys === xs' \\ ys

propDiffCompatR :: [Var] -> [Var] -> [Var] -> Bool
propDiffCompatR xs ys ys' = ys /== ys' || xs \\ ys === xs \\ ys'

propDiffCompatR2 :: [Var] -> [Var] -> [Var] -> Bool
propDiffCompatR2 xs ys ys' = ys /== ys' || xs \\ ys == xs \\ ys'

propDiffCompatR3 :: [Var] -> [Var] -> [Var] -> Bool
propDiffCompatR3 xs ys ys' = (xs /\ ys) /== (xs /\ ys') || xs \\ ys == xs \\ ys'

propDiffCompatLR :: [Var] -> [Var] -> [Var] -> [Var] -> Bool
propDiffCompatLR xs xs' ys ys' = xs /== xs' || ys /== ys' || 
    xs \\ ys === xs' \\ ys'

propDiffInter :: [Var] -> [Var] -> Bool
propDiffInter xs ys = xs \\ ys == xs \\ (xs /\ ys)

propDiffNotIn :: [Var] -> [Var] -> Bool
propDiffNotIn xs ys = not (all (`notElem` xs) ys) || xs \\ ys == xs

propDiffConcat :: [[Var]] -> [Var] -> Bool
propDiffConcat xss ys = not (all (\y -> all (y `notElem`) xss) ys) ||
    concat xss \\ ys == concat xss

propDiffAppend :: [Var] -> [Var] -> Bool
propDiffAppend xs ys = xs ++ ys === xs ++ (ys \\ xs)
