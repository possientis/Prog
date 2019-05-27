module  Fol.Haskell.Test.Variable
    (   specVariable
    )   where

import Test.Hspec
import Test.QuickCheck

import Haskell.Variable (Var)

import Fol.Haskell.P
import Fol.Haskell.Variable

specVariable :: Spec
specVariable = describe "Testing properties of var..." $ 
    sequence_ specsVariable

specsVariable :: [Spec]
specsVariable  = [ testVarFmap
                 ]

testVarFmap :: Spec
testVarFmap = it "Checked var fmap property" $ 
    property $ propVarFmap

propVarFmap :: (Var -> Var) ->  P Var -> Bool
propVarFmap f p = var (fmap f p) == map f (var p)
