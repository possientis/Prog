{-# LANGUAGE TypeApplications       #-}

module  Test.Lam.Main
    (   specLam
    )   where

import Test.Hspec

import Lam.Syntax

import Test.Poly.Main

import Test.Lam.Valid
import Test.Lam.Subst
import Test.Lam.Free
import Test.Lam.BetaValid


specLam :: Spec
specLam = describe "Testing Haskell for Lam..." $ do
    specPoly @ T 
    specValid
    specSubst
    specFree
    specBetaValid

