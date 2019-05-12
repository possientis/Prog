module  Lam.Haskell.Test.Subformula
    (   specSubformula
    )   where

import Test.Hspec
import Test.QuickCheck


import Lam.Haskell.T
import Lam.Haskell.Subformula
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

propReflexivity :: T Var -> Bool
propReflexivity t = t <<= t

propAntiSymmetry :: T Var -> T Var -> Bool
propAntiSymmetry s t = not (s <<= t) || not (t <<= s) ||  (s == t)

propTransitivity :: T Var -> T Var -> T Var -> Bool
propTransitivity r s t = not (r <<= s) || not (s <<= t) || (r <<= t) 
         

