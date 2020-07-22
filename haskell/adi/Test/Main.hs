module  Test.Main
    (   specMain
    )   where

import Test.Hspec

import Test.Eval
import Test.Pretty

specMain :: Spec
specMain = do
    specEval
    specPretty
