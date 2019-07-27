module  Test.Lam.Main
    (   specLam
    )   where

import Test.Hspec

import Test.Lam.T
import Test.Lam.Free
import Test.Lam.Bound
import Test.Lam.Variable
import Test.Lam.Subformula

specLam :: Spec
specLam = sequence_
    [ specT
    , specSubformula
    , specVariable
    , specFree
    , specBound
    ]
