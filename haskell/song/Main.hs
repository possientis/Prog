module  Main
    (   main
    )   where

import Test.QuickCheck

main :: IO ()
main = do
    ls <- generate $ vectorOf 20 arbitrary :: IO [Int]
    print ls
