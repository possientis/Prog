module Test.Lam.Subst
    (   specSubst
    )   where

import Test.Hspec
import Test.QuickCheck

import Variable (Var)
import Lam.T
import Lam.Subst


specSubst :: Spec
specSubst = describe "Testing properties of subst..." $ do
    specSubstVar


specSubstVar :: Spec
specSubstVar = it "Check substVar property" $
    property $ propSubstVar

propSubstVar :: (Var -> T Var) -> Var -> Bool
propSubstVar f x = subst f (Var x) == f x



