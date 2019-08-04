module  Test.Fol.Main
    (   specFol
    )   where

import Test.Hspec

import Test.Fol.P
import Test.Fol.Free
import Test.Fol.Bound
import Test.Fol.Valid
import Test.Fol.Variable
import Test.Fol.Subformula

specFol :: Spec
specFol = sequence_
    [ specP
    , specSubformula
    , specVariable
    , specFree
    , specBound
    , specValid
    ]
