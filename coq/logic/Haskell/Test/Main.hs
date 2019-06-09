module  Haskell.Test.Main
    (   specHask
    )   where

import Test.Hspec

import Haskell.Test.Permute
import Haskell.Test.Replace

specHask :: Spec
specHask = sequence_
    [ specPermute
    , specReplace
    ]
