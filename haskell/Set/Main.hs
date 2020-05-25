module  Main
    (   main
    )   where

import Test.Hspec
import Test.Set

main :: IO ()
main = hspec $ do
    describe "Testing Set..." $ specSet
