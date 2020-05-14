module  Test.Lam.Free
    (   specFree
    )   where

import Test.Hspec
import Test.QuickCheck

import Equiv
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
    testFreeSubstInterGen
    testFreeSubstInter

testFreeSubstGen :: Spec
testFreeSubstGen = it "Checked the free subst gen property" $
    property $ propFreeSubstGen

testFreeSubst :: Spec
testFreeSubst = it "Checked Fr (f t) <= U_{u in Fr(t)} Fr (f u)" $
    property $ propFreeSubst

testFreeSubstInterGen :: Spec
testFreeSubstInterGen = it "Checked Fr(t) /\\ xs = Fr(t) /\\ ys -> ..." $
    property $ propFreeSubstInterGen

testFreeSubstInter :: Spec
testFreeSubstInter = it "Checked Fr(t) /\\ xs = [] -> f*(t)(xs) = f t" $
    property $ propFreeSubstInter

propFreeSubstGen :: (Var -> T Var) -> T Var -> [Var] -> Bool
propFreeSubstGen f t xs = 
    free (subst_ f xs t) <== free t /\ xs ++ concatMap (free . f) (free t \\ xs)

propFreeSubst :: (Var -> T Var) -> T Var -> Bool
propFreeSubst f t = free (subst f t) <== concatMap (free . f) (free t)

propFreeSubstInterGen :: (Var -> T Var) -> T Var -> [Var] -> [Var] -> Bool
propFreeSubstInterGen f t xs ys = (free t /\ xs) /== (free t /\ ys) || 
    subst_ f xs t == subst_ f ys t 

propFreeSubstInter :: (Var -> T Var) -> T Var -> [Var] -> Bool
propFreeSubstInter f t xs = (free t /\ xs) /== [] || subst_ f xs t == subst f t

