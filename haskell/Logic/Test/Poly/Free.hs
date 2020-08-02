{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}

module  Test.Poly.Free
    (   specFree
    )   where

import Test.Hspec
import Test.QuickCheck

import Test.Poly.Test

import Formula
import Variable (Var)

import Func.Replace

import List.Include
import List.InjectiveOn

specFree :: forall f . (Test f) => Spec
specFree = describe "Testing properties of free..." $ do 
    testFreeFmap        @ f
    testFreeVar         @ f
    testFreeInj         @ f 
    testFreeReplace1    @ f
    testFreeReplace2    @ f

testFreeFmap :: forall f . (Test f) =>  Spec
testFreeFmap = it "Checked free fmap property" $ 
    property $ propFreeFmap @ f

testFreeVar :: forall f . (Test f) =>  Spec
testFreeVar = it "Checked free variables are variables" $ 
    property $ propFreeVar @ f

testFreeInj :: forall f . (Test f) =>  Spec
testFreeInj = it "Checked free variables injective property" $ 
    property $ propFreeInj @ f

testFreeReplace1 :: forall f . (Test f) =>  Spec
testFreeReplace1 = it "Checked free first replace property" $ 
    property $ propFreeReplace1 @ f

testFreeReplace2 :: forall f . (Test f) =>  Spec
testFreeReplace2 = it "Checked free second replace property" $ 
    property $ propFreeReplace2 @ f

propFreeFmap :: (Test f) => (Var -> Var) -> f Var -> Bool
propFreeFmap f t = free (fmap f t) <== map f (free t)

propFreeVar :: (Test f) => f Var -> Bool
propFreeVar t = free t <== var t

propFreeInj :: (Test f) => (Var -> Var) -> f Var -> Bool
propFreeInj f t = (not $ injectiveOn (var t) f) || 
    free (fmap f t) == map f (free t)

propFreeReplace1 :: (Test f) => f Var -> Var -> Var -> Bool
propFreeReplace1 t x y = y `elem` var t || x `elem` free t ||
    free (fmap (y <-: x) t) == free t

propFreeReplace2 :: (Test f) => f Var -> Var -> Var -> Var -> Bool
propFreeReplace2 t x y z = y `elem` var t || (not $ x `elem` free t) ||
    (z `elem` free (fmap (y <-: x) t)) == (z == y || (z `elem` free t && z /= x))
