module  Main (main)   where

import Test.Hspec

import Fol.Haskell.Test as Fol
import Lam.Haskell.Test as Lam

main :: IO ()
main = hspec $ do
    Fol.test
    Lam.test
   
    
