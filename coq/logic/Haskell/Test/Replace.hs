module  Haskell.Test.Replace
    (   specReplace
    )   where

import  Test.Hspec
import  Test.QuickCheck

import Haskell.Replace
import Haskell.Variable (Var)

specReplace :: Spec
specReplace = describe "Testing properties for replace (<-:)..." $
    sequence_ specsReplace

specsReplace :: [Spec]
specsReplace  = [ testNotation
                ]

 
testNotation :: Spec
testNotation = it "Checked notation (<-:) coincide with 'flip replace'" $
    property $ propNotation


propNotation :: Var -> Var -> Var -> Bool
propNotation x y u = replace x y u == (y <-: x) u


