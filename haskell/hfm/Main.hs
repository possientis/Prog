module Main 
  ( main 
  ) where

import Eval.App
import Lang.Logger hiding (logMessage)
import Utils

main :: IO ()
main = runApp $ do
  logMessage Info (Message "This is the first message")
  logMessage Info (Message "This is the second message")
  logMessage Info (Message "This is the third message")
