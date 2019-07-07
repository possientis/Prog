module  Test.Fol.Free
    (   specFree
    )   where


import Test.Hspec
import Test.QuickCheck

import Include
import Injective
import Replace
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
             , testFreeReplace1
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

testFreeReplace1 :: Spec
testFreeReplace1 = it "Checked free first replace property" $ 
    property $ propFreeReplace1

propFreeFmap :: (Var -> Var) -> P Var -> Bool
propFreeFmap f p = incl (free (fmap f p)) (map f (free p))

propFreeVar :: P Var -> Bool
propFreeVar p = incl (free p) (var p)

propFreeInj :: (Var -> Var) -> P Var -> Bool
propFreeInj f p = (not $ injective_on (var p) f) || 
    free (fmap f p) == map f (free p)

propFreeReplace1 :: P Var -> Var -> Var -> Bool
propFreeReplace1 p x y = y `elem` var p || x `elem` free p ||
    free (fmap (y <-: x) p) == free p
