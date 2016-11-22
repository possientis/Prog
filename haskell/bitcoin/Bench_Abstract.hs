module Bench_Abstract
  ( logMessage 
  , benchmark
  ) where

import Rand
import Data.Time.Clock.POSIX
import Text.Printf

logMessage :: String -> Rand ()
logMessage s = fromIO $ putStrLn s

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
