{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}

module  Test.Formula
    (   specFormula
    )   where

import Test.Hspec

import Test.Test
import Test.Free
import Test.Bound
import Test.Valid
import Test.Functor
import Test.Variable
import Test.Subformula

specFormula :: forall f . (Test f) =>  Spec
specFormula = sequence_
    [ specFunctor    @ f
    , specSubformula @ f
    , specVariable   @ f
    , specFree       @ f
    , specBound      @ f
    , specValid      @ f
    ]
