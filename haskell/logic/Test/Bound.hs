{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}

module  Test.Bound
    (   specBound
    )   where

import Test.Hspec
import Test.QuickCheck

import Test.Test

import Include
import Formula
import Variable (Var)


specBound :: forall f . (Test f) =>  Spec
specBound = describe "Testing properties of bnd..." $
    sequence_ (specsBound @ f)

specsBound :: forall f . (Test f) =>  [Spec]
specsBound  = [ testBoundVar    @ f
              , testBoundFree   @ f
              , testBoundFmap   @ f
              ]

testBoundVar :: forall f . (Test f) =>  Spec
testBoundVar = it "Checked bound variables are variables" $ 
    property $ propBoundVar @ f

testBoundFree :: forall f . (Test f) =>  Spec
testBoundFree = it "Checked all variables are free or bound" $ 
    property $ propBoundFree @ f

testBoundFmap :: forall f . (Test f) =>  Spec
testBoundFmap = it "Checked bnd fmap property" $
    property $ propBoundFmap @ f

propBoundVar :: (Test f) => f Var -> Bool
propBoundVar t = incl (bnd t) (var t)

propBoundFree :: (Test f) => f Var -> Var -> Bool 
propBoundFree t z = (z `elem` var t) == ((z `elem` free t) || (z `elem` bnd t))

propBoundFmap :: (Test f) => (Var -> Var) -> f Var -> Bool
propBoundFmap f t = bnd (fmap f t) == map f (bnd t)