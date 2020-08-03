{-# LANGUAGE TypeApplications       #-}

module  Test.Fol.Main
    (   specFol
    )   where

import Test.Hspec

import Test.Poly.Main
import Test.Fol.Valid

import Fol.Syntax

specFol :: Spec
specFol = describe "Testing Haskell for Fol..." $ do
    specPoly @ P
    specValid

