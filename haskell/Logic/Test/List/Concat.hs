module  Test.List.Concat
    (   specConcat
    )   where

import  Test.Hspec
import  Test.QuickCheck
    
import Variable (Var)

specConcat :: Spec
specConcat = describe "Testing properties of concat..." $ do
    specConcatCharac


specConcatCharac :: Spec
specConcatCharac = it "Checked concat charac property" $ do
    property $ propConcatCharac

propConcatCharac :: [[Var]] -> Var -> Bool
propConcatCharac xss x = (x `elem` concat xss) == any (x `elem`) xss



