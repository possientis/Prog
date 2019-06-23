module  Test.Fol.Main
    (   specFol
    )   where

import Test.Hspec

import Test.Fol.P
import Test.Fol.Variable
import Test.Fol.Subformula
import Test.Fol.Free

specFol :: Spec
specFol = sequence_
    [ specP
    , specSubformula
    , specVariable
    , specFree
    ]
