{-# LANGUAGE TypeApplications       #-}

module  Test.Eval2
    (   specEval2
    )   where

import Test.Hspec

import Eval2

import Test.Eval

specEval2 :: Spec
specEval2 = describe "Testing monad Eval2" $ do
    specEval @Eval2
