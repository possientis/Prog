{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}

module  Test.Poly.Variable
    (   specVariable
    )   where

import Test.Hspec
import Test.QuickCheck

import Test.Poly.Test

import Formula
import Variable (Var)

import Func.Replace
import Func.Permute

specVariable :: forall f . (Test f) => Spec
specVariable = describe "Testing properties of var..." $ do
    testVarFmap              @ f
    testVarSupport           @ f
    testVarPermuteReplace    @ f
    testVarReplaceTrans      @ f
    testVarReplaceRemove     @ f

testVarFmap :: forall f . (Test f) => Spec
testVarFmap = it "Checked var fmap property" $ 
    property $ propVarFmap @ f

testVarSupport :: forall f . (Test f) =>  Spec
testVarSupport = it "Checked var support property" $ 
    property $ propVarSupport @ f

testVarPermuteReplace :: forall f . (Test f) =>  Spec
testVarPermuteReplace = it "Checked var permute-replace property" $
    property $ propVarPermuteReplace @ f

testVarReplaceTrans :: forall f . (Test f) =>  Spec
testVarReplaceTrans = it "Checked var replace-trans property" $ 
    property $ propVarReplaceTrans @ f

testVarReplaceRemove :: forall f . (Test f) =>  Spec
testVarReplaceRemove = it "Checked var replace-remove property" $
    property $ propVarReplaceRemove @ f

propVarFmap :: (Test f) => (Var -> Var) ->  f Var -> Bool
propVarFmap f t = var (fmap f t) == map f (var t)

propVarSupport :: (Test f) => (Var -> Var) -> (Var -> Var) -> f Var -> Bool
propVarSupport f g t = propVarSupport_naive f g t

-- test is useless, but at least we are able to express lemma's statement
propVarSupport_naive :: (Test f) => (Var -> Var) -> (Var -> Var) -> f Var -> Bool
propVarSupport_naive f g t = 
    ((fmap f t) == (fmap g t) && all (\x -> f x == g x) (var t)) ||
    ((fmap f t) /= (fmap g t) && any (\x -> f x /= g x) (var t)) 

propVarPermuteReplace :: (Test f) =>  Var -> Var -> f Var -> Bool
propVarPermuteReplace x y t = y `elem` var t || 
    fmap (y <-: x) t == fmap (x <-> y) t

propVarReplaceTrans :: (Test f) => Var -> Var -> Var -> f Var -> Bool
propVarReplaceTrans x y z t = y `elem` var t ||
    fmap (z <-: y) (fmap (y <-: x) t) == fmap (z <-: x) t

propVarReplaceRemove :: (Test f) => Var -> Var -> f Var -> Bool
propVarReplaceRemove x y t = x == y || x `notElem` var (fmap (y <-: x) t)

