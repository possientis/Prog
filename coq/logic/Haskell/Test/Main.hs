module  Haskell.Test.Main
    (   specHask
    )   where

import Test.Hspec

import Haskell.Test.Permute
import Haskell.Test.Replace
import Haskell.Test.Include

specHask :: Spec
specHask = sequence_
    [ specPermute
    , specReplace
    , specInclude
    ]
