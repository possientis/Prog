module  Test.Main
    (   main
    )   where

import Test.Hspec

import Test.F13
import Test.R

main :: IO ()
main = hspec $ do
    specF13
    specR
