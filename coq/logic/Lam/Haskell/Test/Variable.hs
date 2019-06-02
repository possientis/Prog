module  Lam.Haskell.Test.Variable
    (   specVariable
    )   where

import Test.Hspec
import Test.QuickCheck

import Haskell.Variable (Var)

import Lam.Haskell.T
import Lam.Haskell.Variable

specVariable :: Spec
specVariable = describe "Testing properties of var..." $ 
    sequence_ specsVariable

specsVariable :: [Spec]
specsVariable  = [ testVarFmap
                 , testVarSupport
                 ]

testVarFmap :: Spec
testVarFmap = it "Checked var fmap property" $ 
    property $ propVarFmap

testVarSupport :: Spec
testVarSupport = it "Checked var support property" $ 
    property $ propVarSupport

propVarFmap :: (Var -> Var) ->  T Var -> Bool
propVarFmap f t = var (fmap f t) == map f (var t)

propVarSupport :: (Var -> Var) -> (Var -> Var) -> T Var -> Bool
propVarSupport f g t = propVarSupport_naive f g t

-- test is useless, but at least we are able to express lemma's statement
propVarSupport_naive :: (Var -> Var) -> (Var -> Var) -> T Var -> Bool
propVarSupport_naive f g t = 
    ((fmap f t) == (fmap g t) && all (\x -> f x == g x) (var t)) ||
    ((fmap f t) /= (fmap g t) && any (\x -> f x /= g x) (var t)) 

