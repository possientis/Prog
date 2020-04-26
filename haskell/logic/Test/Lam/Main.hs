{-# LANGUAGE TypeApplications       #-}

module  Test.Lam.Main
    (   specLam
    )   where

import Test.Hspec

import Test.Formula
import Test.Lam.Valid
import Test.Lam.Subst
import Test.Lam.Free

import Lam.T

specLam :: Spec
specLam = do
    specFormula @ T 
    specValid
    specSubst
    specFree
