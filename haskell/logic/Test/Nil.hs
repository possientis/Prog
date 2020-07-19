module  Test.Nil
    (   specNil
    )   where

import Include
import Variable (Var)

import Test.Hspec
import Test.QuickCheck

specNil :: Spec
specNil = describe "Testing properties of []..." $ do
    testNilCharac

testNilCharac :: Spec
testNilCharac = it "Checked characterization of []" $
    property propNilCharac

-- Approximate fit
propNilCharac :: [Var] -> [Var] -> Bool
propNilCharac xs ys = not (xs <== ys) ||
    (xs == []) == all (`notElem` xs) ys


