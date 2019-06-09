module  Fol.Haskell.Test.Variable
    (   specVariable
    )   where

import Test.Hspec
import Test.QuickCheck

import Haskell.Permute
import Haskell.Replace
import Haskell.Variable (Var)

import Fol.Haskell.P
import Fol.Haskell.Variable

specVariable :: Spec
specVariable = describe "Testing properties of var..." $ 
    sequence_ specsVariable

specsVariable :: [Spec]
specsVariable  = [ testVarFmap
                 , testVarSupport
                 , testVarPermuteReplace
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

propVarFmap :: (Var -> Var) ->  P Var -> Bool
propVarFmap f p = var (fmap f p) == map f (var p)

propVarSupport :: (Var -> Var) -> (Var -> Var) -> P Var -> Bool
propVarSupport f g p = propVarSupport_naive f g p

-- test is useless, but at least we are able to express lemma's statement
propVarSupport_naive :: (Var -> Var) -> (Var -> Var) -> P Var -> Bool
propVarSupport_naive f g p = 
    ((fmap f p) == (fmap g p) && all (\x -> f x == g x) (var p)) ||
    ((fmap f p) /= (fmap g p) && any (\x -> f x /= g x) (var p)) 


propVarPermuteReplace :: Var -> Var -> P Var -> Bool
propVarPermuteReplace x y p = y `elem` var p || 
    fmap (y <-: x) p == fmap (x <-> y) p
