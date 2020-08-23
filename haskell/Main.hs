module  Main
    (   main
    )   where

import System.IO

main :: IO ()
main = do
    handle   <- openFile "alara.txt" ReadMode
    contents <- hGetContents handle
    putStr contents
    hClose handle
