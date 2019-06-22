module  Main (main)   where

import Test.Hspec

import Test.Main
import Test.Fol.Main
import Test.Lam.Main

main :: IO ()
main = hspec $ do
    describe "Testing common Haskell..."  $ specHask
    describe "Testing Haskell for Fol..." $ specFol
    describe "Testing Haskell for Lam..." $ specLam
   
    
