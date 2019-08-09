{-# LANGUAGE TypeApplications       #-}

module  Test.Fol.Main
    (   specFol
    )   where

import Test.Hspec

import Test.Formula
import Test.Fol.Valid

import Fol.P

specFol :: Spec
specFol = sequence_
    [ specFormula @ P
    , specValid
    ]
