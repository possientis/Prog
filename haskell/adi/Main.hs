
module  Main (main)   where

import Test.Hspec
import Test.Main


main :: IO ()
main = seq (error "Fix me") $ hspec $ do
  describe "Testing ADI project ..."  $ specMain
