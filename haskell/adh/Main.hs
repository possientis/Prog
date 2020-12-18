module  Main
    (   main
    )   where

import Test.Hspec
import Test.SymList
import Test.RanAccess

main :: IO ()
main = hspec $ do
    specSymList
    specRanAccess
