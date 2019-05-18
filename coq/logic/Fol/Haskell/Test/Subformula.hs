module  Fol.Haskell.Test.Subformula
    (   specSubformula
    )   where

import Test.Hspec
import Test.QuickCheck


import Fol.Haskell.P
import Fol.Haskell.Order
import Fol.Haskell.Subformula
import Haskell.Variable (Var)

specSubformula :: Spec
specSubformula = describe "Testing properties of subformula order (<<=)..." $
    sequence_ specsSubformula

specsSubformula :: [Spec]
specsSubformula  = [ testReflexivity
                   , testAntiSymmetry
                   , testTransitivity
                   , testSubInclusion
                   , testOrderMonotone
                   , testSubFmap
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

testSubInclusion :: Spec
testSubInclusion = it "Checked (<<=) inclusion property" $
    property $ propSubInclusion

testOrderMonotone :: Spec
testOrderMonotone = it "Checked (<<=) monotone order property" $ 
    property $ propOrderMonotone

testSubFmap :: Spec
testSubFmap = it "Checked (<<=) fmap property" $
    property $ propSubFmap

propReflexivity :: P Var -> Bool
propReflexivity p = p <<= p

propAntiSymmetry :: P Var -> P Var -> Bool
propAntiSymmetry p q = propAntiSymmetry_naive p q && propAntiSymmetry_real q

propAntiSymmetry_naive :: P Var -> P Var -> Bool
propAntiSymmetry_naive  p q = not (p <<= q) || not (q <<= p) ||  (p == q)

propAntiSymmetry_real :: P Var -> Bool
propAntiSymmetry_real q = all f (sub q) where
    f p = not (q <<= p) || (p == q)

propTransitivity :: P Var -> P Var -> P Var -> Bool
propTransitivity p q r = propTransitivity_naive p q r && propTransitivity_real r

propTransitivity_naive :: P Var -> P Var -> P Var -> Bool
propTransitivity_naive p q r = not (p <<= q) || not (q <<= r) || (p <<= r) 
 
propTransitivity_real :: P Var -> Bool
propTransitivity_real r = all f (sub r) where
    f q = all (<<= r) (sub q)

propSubInclusion :: P Var -> P Var -> Bool
propSubInclusion p q = incl (sub p) (sub q) == (p <<= q) where
    incl xs ys = and $ map (\x -> x `elem` ys) xs 

propOrderMonotone :: P Var -> P Var -> Bool
propOrderMonotone p q = not (p <<= q) || (ord p <= ord q)

propSubFmap :: (Var -> Var) -> P Var -> Bool
propSubFmap f p = sub (fmap f p) == map (fmap f) (sub p)
