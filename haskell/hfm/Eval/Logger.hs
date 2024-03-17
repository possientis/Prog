module Eval.Logger
  ( runLogger 
  ) where

import Core.Free
import Lang.Logger

evalLoggerF :: LoggerF a -> IO a
evalLoggerF (LogMessage _lvl msg next) = do
  putStrLn (unMessage msg)
  pure $ next () 

runLogger :: Logger a -> IO a
runLogger = foldFree evalLoggerF
