module  Test.Main
    (   main
    )   where

import Test.Hspec

import Test.Q
import Test.Fp
import Test.F13

main :: IO ()
main = hspec $ do
    specQ
    specFp
    specF13
