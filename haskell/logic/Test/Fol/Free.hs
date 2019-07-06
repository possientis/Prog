module  Test.Fol.Free
    (   specFree
    )   where


import Test.Hspec
import Test.QuickCheck

import Include
import Injective
import Variable (Var)

import Fol.P
import Fol.Free
import Fol.Variable

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

propFreeFmap :: (Var -> Var) -> P Var -> Bool
propFreeFmap f p = incl (free (fmap f p)) (map f (free p))

propFreeVar :: P Var -> Bool
propFreeVar p = incl (free p) (var p)

propFreeInj :: (Var -> Var) -> P Var -> Bool
propFreeInj f p = (not $ injective_on (var p) f) || 
    free (fmap f p) == map f (free p)

