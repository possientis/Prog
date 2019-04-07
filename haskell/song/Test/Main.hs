module  Test.Main
    (   main
    )   where

import Test.Hspec

import Test.Q
import Test.Fp
import Test.F13
import Test.Mod13

main :: IO ()
main = hspec $ do
    specQ
    specF13
    specMod13
    specFp

