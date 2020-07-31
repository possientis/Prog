module  Test.List.InjectiveOn
    (   specInjective
    )   where


import Test.Hspec
import Test.QuickCheck

import Variable (Var)

import List.Include
import List.InjectiveOn

specInjective :: Spec
specInjective = describe "Testing properties for injective functions..." $ do
    testInjective_on_appl
    testInjective_on_appr
    testInjective_on_cons
    testInjective_on_incl
    testInjective_on_not_in

testInjective_on_appl :: Spec
testInjective_on_appl = it "Checked injective left append property" $
    property $ propInjective_on_appl

testInjective_on_appr :: Spec
testInjective_on_appr = it "Checked injective right append property" $
    property $ propInjective_on_appr

testInjective_on_cons :: Spec
testInjective_on_cons = it "Checked injective cons property" $
    property $ propInjective_on_cons

testInjective_on_incl :: Spec
testInjective_on_incl = it "Checked injective incl property" $
    property $ propInjective_on_incl

testInjective_on_not_in :: Spec
testInjective_on_not_in = it "Checked injective 'not in' property" $
    property $ propInjective_on_not_in

propInjective_on_appl :: [Var] -> [Var] -> (Var -> Var) -> Bool
propInjective_on_appl xs ys f = (not $ injectiveOn (xs ++ ys) f) 
    || injectiveOn xs f

propInjective_on_appr :: [Var] -> [Var] -> (Var -> Var) -> Bool
propInjective_on_appr xs ys f = (not $ injectiveOn (xs ++ ys) f) 
    || injectiveOn ys f

propInjective_on_cons :: Var -> [Var] -> (Var -> Var) -> Bool
propInjective_on_cons x xs f = (not $ injectiveOn (x : xs) f) 
    || injectiveOn xs f

propInjective_on_incl :: [Var] -> [Var] -> (Var -> Var) -> Bool
propInjective_on_incl xs ys f = not (xs <== ys) 
    || (not $ injectiveOn ys f) || injectiveOn xs f

propInjective_on_not_in :: Var -> [Var] -> (Var -> Var) -> Bool
propInjective_on_not_in x xs f = (not $ injectiveOn (x : xs) f) 
    || (x `elem` xs)
    || (not $ f x `elem` map f xs)



