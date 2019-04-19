module  Main
    (   main
    )   where

import Test.QuickCheck

--import Syntax
import Variable


main :: IO ()
main = do
   sample (arbitrary :: Gen Var)
