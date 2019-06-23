module  Test.Lam.Free
    (   specFree
    )   where


import Test.Hspec
import Test.QuickCheck

import Include
import Variable (Var)

import Lam.T
import Lam.Free

specFree :: Spec
specFree = describe "Testing properties of free..." $ 
    sequence_ specsFree

specsFree :: [Spec]
specsFree  = [ testFreeFmap
             ]


testFreeFmap :: Spec
testFreeFmap = it "Checked free fmap property" $ 
    property $ propFreeFmap


propFreeFmap :: (Var -> Var) -> T Var -> Bool
propFreeFmap f t = incl (free (fmap f t)) (map f (free t))
