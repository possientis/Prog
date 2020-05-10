module  Test.Main
    (   specMain
    )   where

import Test.Hspec

import Test.Eval

specMain :: Spec
specMain = do
    specEval
