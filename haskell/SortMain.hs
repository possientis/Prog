-- It is so important to benchmark:
-- Do not assume that parallel program is quicker than sequential
-- Do not assume that more cores leads to quicker run
-- see page 589 of 712 for comments
-- ghc source -threaded -o executable
-- ./executable +RTS -N4 (select four processors at runtime)
  
module Main where

import Data.Time.Clock (diffUTCTime, getCurrentTime)
import System.Environment (getArgs)

import System.Random (StdGen, getStdGen, randoms)
import Sorting

--testFunction = sort :: [Int] -> [Int]
testFunction = parSort :: [Int] -> [Int]
--testFunction = sillySort :: [Int] -> [Int]

-- randoms :: (RandomGen g, Random a) => g -> [a]
-- forcing to make sure all random numbers are created before benchmarking sort
-- If we don't do this, sorting algorithm would be interleaved with random number
-- generation, defeating the purpose of benchmarking code. Note that evaluating
-- something like the length of the list would not be enough to ensure every
-- random number has been created. Note than pseudo-random generation requires
-- preceding random number in order to generate the next. Now imagine a dispatch
-- of non evaluated random numbers to different cores...
randomInts :: Int -> StdGen -> [Int]
randomInts k g =  let result = take k (randoms g)
                  in force result `seq` result
main = do
  args <- getArgs
  let count | null args = 1000000
            | otherwise = read (head args)
  input <- randomInts count `fmap` getStdGen
  putStrLn $ "We have " ++ show (length input) ++ " elements to sort."
  start <- getCurrentTime
  let sorted = testFunction input
  -- without asking for the length (before measuring ending time), the sort 
  -- does not happen at all. Common pitfall when benchmarking with lazy eval 
  putStrLn $ "Sorted all " ++ show (length sorted) ++ " elements."
  end <- getCurrentTime
  putStrLn $ show (end `diffUTCTime` start) ++ " elapsed."
