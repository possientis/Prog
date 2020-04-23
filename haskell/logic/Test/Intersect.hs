module  Test.Intersect
    (   specIntersect
    )   where

import Data.List

import Test.Hspec
import Test.QuickCheck

import Intersect
import Variable (Var)


specIntersect :: Spec
specIntersect = describe "Testing properties of intersect..." $
    sequence_ specsIntersect

specsIntersect :: [Spec]
specsIntersect  = [ testInterIntersect
                  , testInterCharac
                  ]

testInterIntersect :: Spec
testInterIntersect = it "Checked inter coincide with GHC 'intersect'" $
    property $ propInterIntersect

testInterCharac :: Spec
testInterCharac = it "Checked inter characterization property" $
    property $ propInterCharac

propInterIntersect :: [Var] -> [Var] -> Bool
propInterIntersect xs ys = xs /\ ys == intersect xs ys

propInterCharac :: [Var] -> [Var] -> Var -> Bool
propInterCharac xs ys z = (z `elem` xs /\ ys) == (z `elem` xs && z `elem` ys)

