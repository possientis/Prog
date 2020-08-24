module  Test.Main
    (   specMain
    )   where

import Test.Hspec

--import Test.Log
--import Test.Eval1
import Test.Eval2
import Test.Pretty

specMain :: Spec
specMain = do
    specPretty
--    specEval1
    specEval2
--    specLog
