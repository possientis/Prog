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
                 ]

testVarFmap :: Spec
testVarFmap = it "Checked var fmap property" $ 
    property $ propVarFmap

propVarFmap :: (Var -> Var) ->  T Var -> Bool
propVarFmap f t = var (fmap f t) == map f (var t)
