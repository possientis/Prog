module  Test.Func.Main
    (   specFunc
    )   where

import Test.Hspec


import Test.Func.Replace
import Test.Func.Permute

specFunc :: Spec
specFunc = describe "Testing Haskell for Func..." $ do
    specPermute
    specReplace
