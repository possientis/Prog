module  Test.Main
    (   specHask
    )   where

import Test.Hspec

import Test.Permute
import Test.Replace
import Test.Include
import Test.Remove
import Test.Coincide
import Test.Injective
import Test.Intersect

specHask :: Spec
specHask = sequence_
    [ specPermute
    , specReplace
    , specInclude
    , specRemove
    , specInjective
    , specCoincide
    , specIntersect
    ]
