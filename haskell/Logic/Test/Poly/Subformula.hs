{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}

module  Test.Poly.Subformula
    (   specSubformula
    )   where

import Test.Hspec
import Test.QuickCheck

import Test.Poly.Test

import List.Include
import Formula
import Variable (Var)


specSubformula :: forall f . (Test f) => Spec
specSubformula = describe "Testing properties of subformula order (<<=)..." $ do
    testReflexivity    @f
    testAntiSymmetry   @f
    testTransitivity   @f
    testSubInclusion   @f
    testOrderMonotone  @f
    testSubFmap        @f
    testSubVar         @f
    testSubBound       @f

testReflexivity :: forall f . (Test f) => Spec
testReflexivity = it "Checked (<<=) is reflexive" $ 
    property $ propReflexivity @f

testAntiSymmetry :: forall f . (Test f) =>  Spec
testAntiSymmetry = it "Checked (<<=) is antisymmetric" $
    property $ propAntiSymmetry @f

testTransitivity :: forall f . (Test f) =>  Spec
testTransitivity = it "Checked (<<=) is transitive" $
    property $ propTransitivity @f

testSubInclusion :: forall f . (Test f) =>  Spec
testSubInclusion = it "Checked (<<=) inclusion property" $
    property $ propSubInclusion @f

testOrderMonotone :: forall f . (Test f) =>  Spec
testOrderMonotone = it "Checked (<<=) monotone order property" $ 
    property $ propOrderMonotone @f

testSubFmap :: forall f . (Test f) =>  Spec
testSubFmap = it "Checked (<<=) fmap property" $
    property $ propSubFmap @f

testSubVar :: forall f . (Test f) =>  Spec
testSubVar = it "Checked (<<=) var inclusion property" $
    property $ propSubVar @f

testSubBound :: forall f . (Test f) =>  Spec
testSubBound = it "Checked (<<=) bnd inclusion property" $
    property $ propSubBound @f

propReflexivity :: (Test f) => f Var -> Bool
propReflexivity t = t <<= t

propAntiSymmetry :: (Test f) => f Var -> f Var -> Bool
propAntiSymmetry s t = propAntiSymmetry_naive s t && propAntiSymmetry_real t

propAntiSymmetry_naive :: (Test f) => f Var -> f Var -> Bool
propAntiSymmetry_naive s t = not (s <<= t) || not (t <<= s) ||  (s == t)

propAntiSymmetry_real :: (Test f) => f Var -> Bool
propAntiSymmetry_real t = all f (sub t) where
    f s = not (t <<= s) || (s == t)

propTransitivity :: (Test f) => f Var -> f Var -> f Var -> Bool
propTransitivity r s t = propTransitivity_naive r s t && propTransitivity_real t

propTransitivity_naive :: (Test f) => f Var -> f Var -> f Var -> Bool
propTransitivity_naive r s t = not (r <<= s) || not (s <<= t) || (r <<= t) 

propTransitivity_real :: (Test f) => f Var -> Bool
propTransitivity_real t = all f (sub t) where
    f s = all (<<= t) (sub s)

propSubInclusion :: (Test f) => f Var -> f Var -> Bool
propSubInclusion s t =  propSubInclusion_naive s t 
                     && propSubInclusion_real1 t
                     && propSubInclusion_real2 t

propSubInclusion_naive :: (Test f) => f Var -> f Var -> Bool
propSubInclusion_naive s t = (sub s <== sub t) == (s <<= t)

propSubInclusion_real1 :: (Test f) => f Var -> Bool
propSubInclusion_real1 t = all f (sub t) where
    f s = sub s <== sub t
         
propSubInclusion_real2 :: (Test f) => f Var -> Bool
propSubInclusion_real2 t = all (<<= t) (sub t) where 

propOrderMonotone :: (Test f) => f Var -> f Var -> Bool
propOrderMonotone s t = propOrderMonotone_naive s t && propOrderMonotone_real t

propOrderMonotone_naive :: (Test f) => f Var -> f Var -> Bool
propOrderMonotone_naive s t = not (s <<= t) || (ord s <= ord t)

propOrderMonotone_real :: (Test f) => f Var -> Bool
propOrderMonotone_real t = all f (sub t) where
    f s = (ord s <= ord t)

propSubFmap :: (Test f) => (Var -> Var) -> f Var -> Bool
propSubFmap f t = sub (fmap f t) == map (fmap f) (sub t)

propSubVar :: (Test f) => f Var -> f Var -> Bool
propSubVar s t =  propSubVar_naive s t
               && propSubVar_real t

propSubVar_naive :: (Test f) => f Var -> f Var -> Bool
propSubVar_naive s t = not (s <<= t) || var s <== var t

propSubVar_real :: (Test f) => f Var -> Bool
propSubVar_real t = all f (sub t) where
    f s = var s <== var t

propSubBound :: (Test f) => f Var -> f Var -> Bool
propSubBound s t = not (s <<= t) || bnd s <== bnd t

