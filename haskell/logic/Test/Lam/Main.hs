module  Test.Lam.Main
    (   specLam
    )   where

import Test.Hspec

import Test.Lam.T
import Test.Lam.Variable
import Test.Lam.Subformula
import Test.Lam.Free

specLam :: Spec
specLam = sequence_
    [ specT
    , specSubformula
    , specVariable
    , specFree
    ]
