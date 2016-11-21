module Bench_Abstract
  ( logMessage 
  , benchmark
  ) where

import Rand
import Data.Time.Clock.POSIX
import Text.Printf

logMessage :: String -> Rand ()
logMessage s = fromIO $ putStrLn s

benchmark :: Rand a -> String -> Int -> Rand ()
benchmark action name iterations = do

    
  let go n
        | n <= 0    = return ()
        | otherwise = do
          action
          go (n-1)  :: Rand ()

  start <- fromIO getPOSIXTime

  go iterations

  end <- fromIO getPOSIXTime
  
  let time = realToFrac $ (end - start) :: Double 

  fromIO $ printf "Benchmark: %s, %d iterations ran in %.3f seconds\n" 
    name iterations time

{-
test :: IO ()
test = toIO $ do
  benchmark (logMessage "Hello World") "logMessage" 1000
-}
