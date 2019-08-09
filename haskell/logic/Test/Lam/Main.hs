{-# LANGUAGE TypeApplications       #-}

module  Test.Lam.Main
    (   specLam
    )   where

import Test.Hspec

import Test.Formula
import Test.Lam.Valid

import Lam.T

specLam :: Spec
specLam = sequence_
    [ specFormula @ T 
    , specValid
    ]
