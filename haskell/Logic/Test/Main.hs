module  Test.Main
    (   specHask
    )   where

import Test.Hspec

import Test.Nil
import Test.List.Equiv
import Test.Concat
import Test.Remove
import Test.Append
import Test.Permute
import Test.Replace
import Test.List.Include
import Test.List.Coincide
import Test.List.Intersect
import Test.List.Difference
import Test.List.InjectiveOn

specHask :: Spec
specHask = do
    specPermute
    specReplace
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
