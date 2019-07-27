module  Test.Lam.Bound
    (   specBound
    )   where

import Test.Hspec
import Test.QuickCheck

import Include
import Variable (Var)

import Lam.T
import Lam.Free
import Lam.Bound
import Lam.Variable

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

propBoundVar :: T Var -> Bool
propBoundVar t = incl (bnd t) (var t)

propBoundFree :: T Var -> Var -> Bool 
propBoundFree t z = (z `elem` var t) == ((z `elem` free t) || (z `elem` bnd t))
