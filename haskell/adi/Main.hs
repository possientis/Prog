
module  Main (main)   where

import Test.Hspec
import Test.Main


main :: IO ()
main = hspec $ do
    describe "Testing ADI project ..."  $ specMain
