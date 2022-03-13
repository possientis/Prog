module Main
    ( main
    ) where

import FfiLib

main :: IO ()
main = do
    print $ double 2
    print $ triple 2
