module  Test.Main
    (   main
    )   where

import Test.Hspec

import Test.R
import Test.Fp
import Test.F13

main :: IO ()
main = hspec $ do
    specF13
    specFp
    specR
