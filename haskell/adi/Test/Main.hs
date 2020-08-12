module  Test.Main
    (   specMain
    )   where

import Test.Hspec

import Test.Eval1
import Test.Pretty

specMain :: Spec
specMain = do
    specEval1
    specPretty
