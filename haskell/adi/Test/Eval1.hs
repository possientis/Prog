{-# LANGUAGE TypeApplications       #-}

module  Test.Eval1
    (   specEval1
    )   where

import Test.Hspec

import Eval1

import Test.Eval

specEval1 :: Spec
specEval1 = describe "Testing monad Eval1" $ do
    specEval @ Eval1
