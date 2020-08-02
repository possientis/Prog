module  Test.Main (specTest)   where

import Test.Hspec

import Test.Lam.Main
import Test.Fol.Main
import Test.Func.Main
import Test.List.Main

specTest :: Spec
specTest = do
    specFunc
    specList
    specFol
    specLam

