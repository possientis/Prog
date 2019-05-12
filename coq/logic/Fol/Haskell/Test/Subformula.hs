module  Fol.Haskell.Test.Subformula
    (   specSubformula
    )   where

import Test.Hspec
import Test.QuickCheck


import Fol.Haskell.P
import Fol.Haskell.Subformula
import Haskell.Variable (Var)

specSubformula :: Spec
specSubformula = describe "Testing properties of subformula order (<<=)..." $
    sequence_ specsSubformula

specsSubformula :: [Spec]
specsSubformula = [ testReflexivity
                  , testAntiSymmetry
                  , testTransitivity
                  ]

testReflexivity :: Spec
testReflexivity = it "Checked (<<=) is reflexive" $ 
    property $ propReflexivity

testAntiSymmetry :: Spec
testAntiSymmetry = it "Checked (<<=) is antisymmetric" $
    property $ propAntiSymmetry

testTransitivity :: Spec
testTransitivity = it "Checked (<<=) is transitive" $
    property $ propTransitivity

propReflexivity :: P Var -> Bool
propReflexivity p = p <<= p

propAntiSymmetry :: P Var -> P Var -> Bool
propAntiSymmetry p q = not (p <<= q) || not (q <<= p) ||  (p == q)

propTransitivity :: P Var -> P Var -> P Var -> Bool
propTransitivity p q r = not (p <<= q) || not (q <<= r) || (p <<= r) 
 
