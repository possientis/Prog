module  Test.Lam.Free
    (   specFree
    )   where

import Test.Hspec
import Test.QuickCheck

import Include
import Formula
import Variable     (Var)
import Intersect
import Difference

import Lam.T
import Lam.Subst

specFree :: Spec
specFree = describe "Testing non-polymorphic properties of free..." $ do
    testFreeSubstGen
    testFreeSubst

testFreeSubstGen :: Spec
testFreeSubstGen = it "Checked the free subst gen property" $
    property $ propFreeSubstGen

testFreeSubst :: Spec
testFreeSubst = it "Checked the free subst property" $
    property $ propFreeSubst

propFreeSubstGen :: (Var -> T Var) -> T Var -> [Var] -> Bool
propFreeSubstGen f t xs = incl (free $ subst_ f xs t) $
    free t /\ xs ++ concatMap (free . f) (free t \\ xs)

propFreeSubst :: (Var -> T Var) -> T Var -> Bool
propFreeSubst f t = incl (free $ subst f t) . concatMap (free . f) $ free t

