{-# LANGUAGE BangPatterns #-}

module Bench_Abstract
  ( logMessage 
  , benchmark
  ) where

import Rand
import Data.Time.Clock (NominalDiffTime)
import Data.Time.Clock.POSIX
import Text.Printf
import Control.Monad (replicateM_, replicateM)
import Control.Monad.IO.Class

logMessage :: String -> Rand ()
logMessage s = liftIO $ putStrLn s

{- some interesting analysing in Real World Haskell 
 - in relation to measuring code performance, page 548 (588 of 712)
 -
 - "Nonstrict evaluation can turn performance measurement and
 - analysis into something of a minefield"
 -
 - 1. Because of lazy evaluation, we may start the clock before
 - some evaluation has taken place, evaluation which is not meant 
 - to be part of the measured tasks. So we should make sure all
 - prior calculations have effectively taken place before starting
 - the clock.
 -
 - 2. Beware of invisible data dependencies: for example, simply 
 - printing the length of a list does not perform enough evaluation.
 - It would evaluate the spine of the list, but not its elements.
 - So referring to previous point 1., you may think all calculations
 - have been carried out prior to starting the clock, when in fact
 - more work needs to be done.
 -
 - 3. Don't benchmark a thunk. Make sure the code you intend to 
 - evaluate is indeed running  
 -
 - 4. remember to use the runtime option -sstderr in order to get
 - valuable information on memory usgage. 
 -
 - $ ./myProg args +RTS -sstderr
 -
 - In order for runtime options to be available, the source needs to 
 - linked with the -rtsopts option.
 -
 - $ ghc myProg.hs -rtsopts
 -}

{-
time :: MonadIO m => m a -> m NominalDiffTime
time action = do
  start <- liftIO getPOSIXTime
  action
  end <- liftIO getPOSIXTime
  let !delta = end - start
  return delta

benchmark action name iterations = do
  !overhead <- time $ replicateM_ iterations (return ())
  !delta <- time $ replicateM_ iterations action
  let diff = realToFrac (delta - overhead) :: Double
  liftIO $ printf "Benchmark: %s, %d iterations ran in %.3f seconds\n" 
    name iterations diff
-}
  




{-
benchmark :: MonadIO m => m a -> String -> Int -> m ()
benchmark action name iterations = do
  time   <- realToFrac <$> runAction action iterations
  liftIO $ printf "Benchmark: %s, %d iterations ran in %.3f seconds\n" 
    name iterations (time :: Double)

runAction :: MonadIO m => m a -> Int -> m NominalDiffTime
runAction action iterations= sum <$> replicateM iterations action'
  where
    action' = do
      start <- liftIO getPOSIXTime
      action
      end <- liftIO getPOSIXTime
      let !delta = end - start
      return delta
-}

{-
runAction :: MonadIO m => m a -> Int -> m NominalDiffTime
runAction action iterations
  | iterations <= 0   = return 0
  | otherwise         = do
    start <- liftIO getPOSIXTime
    action
    end <- liftIO getPOSIXTime
    rest <- runAction action (iterations -1)
    let total = end - start + rest
    total `seq` return total
-}


-- original post

benchmark action name iterations = do
  start <- liftIO getPOSIXTime
  runAction action iterations
  end <- liftIO getPOSIXTime
  let time = realToFrac $ (end - start) :: Double 
  liftIO $ printf "Benchmark: %s, %d iterations ran in %.3f seconds\n" 
    name iterations time

runAction :: Monad m => m a -> Int -> m ()
runAction action iterations
  | iterations <= 0   = return ()
  | otherwise         = do
    action
    runAction action (iterations -1)

