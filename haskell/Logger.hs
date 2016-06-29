module Logger
  (
    Logger
  , Log
  , runLogger
  , record
  ) where

type Log = [String]
data Logger a = Logger a

runLogger :: Logger a -> (a, Log)
runLogger = undefined


record :: String -> Logger ()
record = undefined


