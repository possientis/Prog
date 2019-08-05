{-# LANGUAGE TypeApplications       #-}

module  Main (main)   where

import Test.Hspec

import Test.Main
import Test.Formula

import Lam.T
import Fol.P

main :: IO ()
main = hspec $ do
    describe "Testing common Haskell..."  $ specHask
    describe "Testing Haskell for Fol..." $ specFormula @ P
    describe "Testing Haskell for Lam..." $ specFormula @ T
   
    
