module  Lam.Haskell.Test.Subformula
    (   specSubformula
    )   where

import Test.Hspec
import Test.QuickCheck


import Lam.Haskell.T
import Lam.Haskell.Order
import Lam.Haskell.Subformula
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
propSubInclusion s t = incl (sub s) (sub t) == (s <<= t) where
    incl xs ys = and $ map (\x -> x `elem` ys) xs 

propOrderMonotone :: T Var -> T Var -> Bool
propOrderMonotone s t = not (s <<= t) || (ord s <= ord t)

propSubFmap :: (Var -> Var) -> T Var -> Bool
propSubFmap f t = sub (fmap f t) == map (fmap f) (sub t)
