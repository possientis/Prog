module  Test.Lam.Variable
    (   specVariable
    )   where

import Test.Hspec
import Test.QuickCheck

import Permute
import Replace
import Variable (Var)

import Lam.T
import Lam.Variable

specVariable :: Spec
specVariable = describe "Testing properties of var..." $ 
    sequence_ specsVariable

specsVariable :: [Spec]
specsVariable  = [ testVarFmap
                 , testVarSupport
                 , testVarPermuteReplace
                 , testVarReplaceTrans
                 , testVarReplaceRemove
                 ]

testVarFmap :: Spec
testVarFmap = it "Checked var fmap property" $ 
    property $ propVarFmap

testVarSupport :: Spec
testVarSupport = it "Checked var support property" $ 
    property $ propVarSupport

testVarPermuteReplace :: Spec
testVarPermuteReplace = it "Checked var permute-replace property" $
    property $ propVarPermuteReplace

testVarReplaceTrans :: Spec
testVarReplaceTrans = it "Checked var replace-trans property" $ 
    property $ propVarReplaceTrans

testVarReplaceRemove :: Spec
testVarReplaceRemove = it "Checked var replace-remove property" $
    property $ propVarReplaceRemove

propVarFmap :: (Var -> Var) ->  T Var -> Bool
propVarFmap f t = var (fmap f t) == map f (var t)

propVarSupport :: (Var -> Var) -> (Var -> Var) -> T Var -> Bool
propVarSupport f g t = propVarSupport_naive f g t

-- test is useless, but at least we are able to express lemma's statement
propVarSupport_naive :: (Var -> Var) -> (Var -> Var) -> T Var -> Bool
propVarSupport_naive f g t = 
    ((fmap f t) == (fmap g t) && all (\x -> f x == g x) (var t)) ||
    ((fmap f t) /= (fmap g t) && any (\x -> f x /= g x) (var t)) 

propVarPermuteReplace :: Var -> Var -> T Var -> Bool
propVarPermuteReplace x y t = y `elem` var t || 
    fmap (y <-: x) t == fmap (x <-> y) t

propVarReplaceTrans :: Var -> Var -> Var -> T Var -> Bool
propVarReplaceTrans x y z t = y `elem` var t ||
    fmap (z <-: y) (fmap (y <-: x) t) == fmap (z <-: x) t

propVarReplaceRemove :: Var -> Var -> T Var -> Bool
propVarReplaceRemove x y t = x == y || x `notElem` var (fmap (y <-: x) t)
