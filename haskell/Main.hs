module Main where

import Data.Char (toUpper)
import Control.Monad

shout = map toUpper

main = putStrLn "Write your string: " >> fmap shout getLine >>= putStrLn

main' = do
  putStrLn "Write your string: "
  line <- getLine
  putStrLn $ shout line


speakTo :: (String -> String) -> IO String
speakTo fSentence = fmap fSentence getLine


sayHello :: IO String
sayHello = speakTo (\name -> "Hello, " ++ name ++ "!")

main2 = do
  x <- readLn :: IO Int
  print x

main3 = (readLn :: IO Int) >>= print
