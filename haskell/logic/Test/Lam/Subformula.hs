module  Test.Lam.Subformula
    (   specSubformula
    )   where

import Test.Hspec
import Test.QuickCheck

import Include
import Variable (Var)

import Lam.T
import Lam.Order
import Lam.Subformula
import Lam.Variable

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

propReflexivity :: T Var -> Bool
propReflexivity t = t <<= t

propAntiSymmetry :: T Var -> T Var -> Bool
propAntiSymmetry s t = propAntiSymmetry_naive s t && propAntiSymmetry_real t

propAntiSymmetry_naive :: T Var -> T Var -> Bool
propAntiSymmetry_naive s t = not (s <<= t) || not (t <<= s) ||  (s == t)

propAntiSymmetry_real :: T Var -> Bool
propAntiSymmetry_real t = all f (sub t) where
    f s = not (t <<= s) || (s == t)

propTransitivity :: T Var -> T Var -> T Var -> Bool
propTransitivity r s t = propTransitivity_naive r s t && propTransitivity_real t

propTransitivity_naive :: T Var -> T Var -> T Var -> Bool
propTransitivity_naive r s t = not (r <<= s) || not (s <<= t) || (r <<= t) 

propTransitivity_real :: T Var -> Bool
propTransitivity_real t = all f (sub t) where
    f s = all (<<= t) (sub s)

propSubInclusion :: T Var -> T Var -> Bool
propSubInclusion s t =  propSubInclusion_naive s t 
                     && propSubInclusion_real1 t
                     && propSubInclusion_real2 t

propSubInclusion_naive :: T Var -> T Var -> Bool
propSubInclusion_naive s t = incl (sub s) (sub t) == (s <<= t)

propSubInclusion_real1 :: T Var -> Bool
propSubInclusion_real1 t = all f (sub t) where
    f s = incl (sub s) (sub t) 
         
propSubInclusion_real2 :: T Var -> Bool
propSubInclusion_real2 t = all (<<= t) (sub t) where 

propOrderMonotone :: T Var -> T Var -> Bool
propOrderMonotone s t = propOrderMonotone_naive s t && propOrderMonotone_real t

propOrderMonotone_naive :: T Var -> T Var -> Bool
propOrderMonotone_naive s t = not (s <<= t) || (ord s <= ord t)

propOrderMonotone_real :: T Var -> Bool
propOrderMonotone_real t = all f (sub t) where
    f s = (ord s <= ord t)

propSubFmap :: (Var -> Var) -> T Var -> Bool
propSubFmap f t = sub (fmap f t) == map (fmap f) (sub t)

propSubVar :: T Var -> T Var -> Bool
propSubVar s t =  propSubVar_naive s t
               && propSubVar_real t

propSubVar_naive :: T Var -> T Var -> Bool
propSubVar_naive s t = not (s <<= t) || incl (var s) (var t) 

propSubVar_real :: T Var -> Bool
propSubVar_real t = all f (sub t) where
    f s = incl (var s) (var t)



