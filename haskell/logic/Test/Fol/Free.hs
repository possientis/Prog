module  Test.Fol.Free
    (   specFree
    )   where


import Test.Hspec
import Test.QuickCheck

import Include
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
             ]


testFreeFmap :: Spec
testFreeFmap = it "Checked free fmap property" $ 
    property $ propFreeFmap

testFreeVar :: Spec
testFreeVar = it "Checked free variables are variables" $ 
    property $ propFreeVar

propFreeFmap :: (Var -> Var) -> P Var -> Bool
propFreeFmap f p = incl (free (fmap f p)) (map f (free p))

propFreeVar :: P Var -> Bool
propFreeVar p = incl (free p) (var p)
