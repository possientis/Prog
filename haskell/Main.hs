module  Main
    (   main
    )   where

import System.IO
import System.Random

main :: IO ()
main = do
    handle   <- openFile "alara.txt" ReadMode
    contents <- hGetContents handle
    putStr contents
    hClose handle
