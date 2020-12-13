module  Main
    (   main
    )   where

import Test.Hspec
import Test.SymList

main :: IO ()
main = hspec $ do
    specSymList
