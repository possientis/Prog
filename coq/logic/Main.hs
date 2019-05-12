module  Main (main)   where

import Test.Hspec

import Fol.Haskell.Test.Main
import Lam.Haskell.Test.Main

main :: IO ()
main = hspec $ do
    describe "Testing Haskell for Fol..." $ specFol
    describe "Testing Haskell for Lam..." $ specLam
   
    
