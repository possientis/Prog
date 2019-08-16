{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}

module  Test.Valid
    (   specValid
    )   where


import Test.Hspec
import Test.QuickCheck

import Test.Test

import Formula
import Replace
import Variable (Var)
import Injective


specValid :: forall f . (Test f) =>  Spec
specValid = describe "Testing properties of valid..." $ 
    sequence_ (specsValid @ f)

specsValid :: forall f . (Test f) =>  [Spec]
specsValid  = [ testValidSub        @ f
              , testValidFree       @ f
              , testValidInj        @ f
              , testValidReplace    @ f
              ]

testValidSub :: forall f . (Test f) =>  Spec
testValidSub = it "Checked valid subformula property" $
    property $ propValidSub @ f

testValidFree :: forall f . (Test f) =>  Spec
testValidFree = it "Checked valid free property" $
    property $ propValidFree @ f

testValidInj :: forall f . (Test f) =>  Spec
testValidInj = it "Checked valid injective property" $
    property $ propValidInj @ f

testValidReplace :: forall f . (Test f) =>  Spec
testValidReplace = it "Checked valid replace property" $
    property $ propValidReplace @ f

propValidSub :: (Test f) =>  (Var -> Var) -> f Var -> Bool
propValidSub f t = valid f t == all (valid f) (sub t)

propValidFree :: (Test f) => (Var -> Var) -> f Var -> Bool
propValidFree f t = valid f t == (all cond (sub t)) where
    cond s = free (fmap f s) == map f (free s) 

propValidInj :: (Test f) => (Var -> Var) -> f Var -> Bool
propValidInj f t = (not $ injective_on (var t) f) || valid f t

propValidReplace :: (Test f) => Var -> Var -> f Var -> Bool
propValidReplace x y t = y `elem` var t || valid (y <-: x) t


