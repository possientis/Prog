module Test.Main
  ( main
  ) where

import Test.Hspec
import qualified Test.Lens as Lens

main :: IO ()
main = hspec $ do
  Lens.spec
