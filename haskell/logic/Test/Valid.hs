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
import Include
import Variable (Var)
import Injective


specValid :: forall f . (Test f) =>  Spec
specValid = describe "Testing properties of valid..." $ do 
    testValidSub        @ f
    testValidFree       @ f
    testValidInj        @ f
    testValidReplace    @ f
    testValidCompose    @ f 
    testValidFmap       @ f
    testValidBound      @ f

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

testValidCompose :: forall f . (Test f) =>  Spec
testValidCompose = it "Checked valid compose property" $
    property $ propValidCompose @ f

testValidFmap :: forall f . (Test f) =>  Spec
testValidFmap = it "Checked valid fmap property" $
    property $ propValidFmap @ f

testValidBound :: forall f . (Test f) =>  Spec
testValidBound = it "Checked valid bound property" $
    property $ propValidBound @ f

propValidSub :: (Test f) =>  (Var -> Var) -> f Var -> Bool
propValidSub f t = valid f t == all (valid f) (sub t)

propValidFree :: (Test f) => (Var -> Var) -> f Var -> Bool
propValidFree f t = valid f t == (all cond (sub t)) where
    cond s = free (fmap f s) == map f (free s) 

propValidInj :: (Test f) => (Var -> Var) -> f Var -> Bool
propValidInj f t = (not $ injective_on (var t) f) || valid f t

propValidReplace :: (Test f) => Var -> Var -> f Var -> Bool
propValidReplace x y t = y `elem` var t || valid (y <-: x) t

propValidCompose :: (Test f) => (Var -> Var) -> (Var -> Var) -> f Var -> Bool
propValidCompose f g t = ((valid f t) && (valid g $ fmap f t)) == valid (g . f) t

propValidFmap :: (Test f) => (Var -> Var) -> (Var -> Var) -> f Var -> Bool
propValidFmap f g t = (fmap f t) /= (fmap g t) || (not $ valid f t) || valid g t

propValidBound :: (Test f) => (Var -> Var) -> f Var -> [Var] -> Bool
propValidBound f t xs = valid f t
                      || not (bnd t <== xs)
                      || not (injective_on xs f)
                      || any g [(x,y) | x <- xs, y <- var t, y `notElem` xs]  
    where g (x,y) = f x == f y



