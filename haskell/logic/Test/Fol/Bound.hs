module  Test.Fol.Bound
    (   specBound
    )   where

import Test.Hspec
import Test.QuickCheck

import Include
import Variable (Var)

import Fol.P
import Fol.Free
import Fol.Bound
import Fol.Variable

specBound :: Spec
specBound = describe "Testing properties of bnd..." $
    sequence_ specsBound

specsBound :: [Spec]
specsBound  = [ testBoundVar
              , testBoundFree
              ]

testBoundVar :: Spec
testBoundVar = it "Checked bound variables are variables" $ 
    property $ propBoundVar

testBoundFree :: Spec
testBoundFree = it "Checked all variables are free or bound" $ 
    property $ propBoundFree

propBoundVar :: P Var -> Bool
propBoundVar p = incl (bnd p) (var p)

propBoundFree :: P Var -> Var -> Bool 
propBoundFree p z = (z `elem` var p) == ((z `elem` free p) || (z `elem` bnd p))
