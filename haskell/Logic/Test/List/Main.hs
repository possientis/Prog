module  Test.List.Main
    (   specList
    )   where

import Test.Hspec

import Test.List.Nil
import Test.List.Equiv
import Test.List.Concat
import Test.List.Remove
import Test.List.Append
import Test.List.Include
import Test.List.Coincide
import Test.List.Intersect
import Test.List.Difference
import Test.List.InjectiveOn

specList :: Spec
specList = describe "Testing Haskell for List..." $ do
    specInclude
    specRemove
    specInjective
    specCoincide
    specIntersect
    specDifference
    specConcat 
    specEquiv
    specAppend
    specNil
