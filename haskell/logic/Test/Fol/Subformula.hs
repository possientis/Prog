module  Test.Fol.Subformula
    (   specSubformula
    )   where

import Test.Hspec
import Test.QuickCheck

import Include
import Variable (Var)

import Fol.P
import Fol.Order
import Fol.Subformula
import Fol.Variable

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
                   , testSubVar
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

testSubVar :: Spec
testSubVar = it "Checked (<<=) var inclusion property" $
    property $ propSubVar

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
propSubInclusion p q =  propSubInclusion_naive p q 
                     && propSubInclusion_real1 q
                     && propSubInclusion_real2 q

propSubInclusion_naive :: P Var -> P Var -> Bool
propSubInclusion_naive p q = incl (sub p) (sub q) == (p <<= q)

propSubInclusion_real1 :: P Var -> Bool
propSubInclusion_real1 q = all f (sub q) where
    f p = incl (sub p) (sub q) 
         
propSubInclusion_real2 :: P Var -> Bool
propSubInclusion_real2 q = all (<<= q) (sub q) where 

propOrderMonotone :: P Var -> P Var -> Bool
propOrderMonotone p q = propOrderMonotone_naive p q && propOrderMonotone_real q

propOrderMonotone_naive :: P Var -> P Var -> Bool
propOrderMonotone_naive p q = not (p <<= q) || (ord p <= ord q)

propOrderMonotone_real :: P Var -> Bool
propOrderMonotone_real q = all f (sub q) where
    f p = (ord p <= ord q)

propSubFmap :: (Var -> Var) -> P Var -> Bool
propSubFmap f p = sub (fmap f p) == map (fmap f) (sub p)

propSubVar :: P Var -> P Var -> Bool
propSubVar p q =  propSubVar_naive p q
               && propSubVar_real q

propSubVar_naive :: P Var -> P Var -> Bool
propSubVar_naive p q = not (p <<= q) || incl (var p) (var q) 

propSubVar_real :: P Var -> Bool
propSubVar_real q = all f (sub q) where
    f p = incl (var p) (var q)


