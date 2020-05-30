module  Main
    (   main
    )   where

import Test.Hspec
import Test.Set
import Test.Normal

main :: IO ()
main = hspec $ do
    describe "Testing Set..."       $ specSet
    describe "Testing Normal..."    $ specNormal
