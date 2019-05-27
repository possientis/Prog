module  Lam.Haskell.Test.Main
    (   specLam
    )   where

import Test.Hspec

import Lam.Haskell.Test.T
import Lam.Haskell.Test.Variable
import Lam.Haskell.Test.Subformula

specLam :: Spec
specLam = sequence_
    [ specT
    , specSubformula
    , specVariable
    ]
