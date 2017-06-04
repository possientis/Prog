module Main where

import System.Environment
import Parse

main :: IO ()
main = do
  args <- getArgs
  putStrLn $ readExpr (args !! 0)

