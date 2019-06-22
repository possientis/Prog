module  Test.Main
    (   specHask
    )   where

import Test.Hspec

import Test.Permute
import Test.Replace
import Test.Include

specHask :: Spec
specHask = sequence_
    [ specPermute
    , specReplace
    , specInclude
    ]
