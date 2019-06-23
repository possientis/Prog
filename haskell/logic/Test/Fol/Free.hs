module  Test.Fol.Free
    (   specFree
    )   where


import Test.Hspec
import Test.QuickCheck

import Include
import Variable (Var)

import Fol.P
import Fol.Free

specFree :: Spec
specFree = describe "Testing properties of free..." $ 
    sequence_ specsFree

specsFree :: [Spec]
specsFree  = [ testFreeFmap
             ]


testFreeFmap :: Spec
testFreeFmap = it "Checked free fmap property" $ 
    property $ propFreeFmap


propFreeFmap :: (Var -> Var) -> P Var -> Bool
propFreeFmap f p = incl (free (fmap f p)) (map f (free p))
