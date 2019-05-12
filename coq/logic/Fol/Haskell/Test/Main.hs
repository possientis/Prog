module  Fol.Haskell.Test.Main
    (   specFol
    )   where

import Test.Hspec

import Fol.Haskell.Test.P
import Fol.Haskell.Test.Subformula

specFol :: Spec
specFol = sequence_
    [ specP
    , specSubformula
    ]
