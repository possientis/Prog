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
    specSubstX


specSubstX :: Spec
specSubstX = it "Check substx property" $
    property $ propSubstX

propSubstX :: (Var -> T Var) -> Var -> Bool
propSubstX f x = subst f (Var x) == f x



