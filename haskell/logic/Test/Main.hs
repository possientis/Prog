module  Test.Main
    (   specHask
    )   where

import Test.Hspec

import Test.Equiv
import Test.Concat
import Test.Remove
import Test.Permute
import Test.Replace
import Test.Include
import Test.Coincide
import Test.Injective
import Test.Intersect
import Test.Difference
import Test.Append

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
