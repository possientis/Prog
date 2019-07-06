module  Test.Lam.Free
    (   specFree
    )   where


import Test.Hspec
import Test.QuickCheck

import Include
import Injective
import Variable (Var)

import Lam.T
import Lam.Free
import Lam.Variable

specFree :: Spec
specFree = describe "Testing properties of free..." $ 
    sequence_ specsFree

specsFree :: [Spec]
specsFree  = [ testFreeFmap
             , testFreeVar
             , testFreeInj
             ]


testFreeFmap :: Spec
testFreeFmap = it "Checked free fmap property" $ 
    property $ propFreeFmap

testFreeVar :: Spec
testFreeVar = it "Checked free variables are variables" $ 
    property $ propFreeVar

testFreeInj :: Spec
testFreeInj = it "Checked free variables injective property" $ 
    property $ propFreeInj

propFreeFmap :: (Var -> Var) -> T Var -> Bool
propFreeFmap f t = incl (free (fmap f t)) (map f (free t))

propFreeVar :: T Var -> Bool
propFreeVar t = incl (free t) (var t)

propFreeInj :: (Var -> Var) -> T Var -> Bool
propFreeInj f t = (not $ injective_on (var t) f) || 
    free (fmap f t) == map f (free t)

