module  Test.Difference
    (   specDifference
    )   where

import Test.Hspec
import Test.QuickCheck

import Difference
import Variable (Var)

specDifference :: Spec
specDifference = describe "Testing properties of difference..." $
    sequence_ specsDifference

specsDifference :: [Spec]
specsDifference  = [ testDiffCharac
                   ]

testDiffCharac :: Spec
testDiffCharac = it "Checked diff characterization property" $ 
    property $ propDiffCharac


propDiffCharac :: [Var] -> [Var] -> Var -> Bool
propDiffCharac xs ys z = (z `elem` diff xs ys) == (z `elem` xs && z `notElem` ys)
