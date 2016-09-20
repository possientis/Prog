{-# LANGUAGE BangPatterns #-}

-- ghc G.hs -rtsopts (if you want to use +RTS options)
-- ./G 1e7 +RTS -sstderr

-- WARNING --
-- Do not use ghci to assess performance of the code

import System.Environment (getArgs)
import Data.List(foldl')
import Text.Printf (printf)

data Pair = Pair !Int !Double  -- creating a strict data type


mean :: [Double] -> Double
mean xs = s / fromIntegral n
  where
    Pair n s = foldl' k (Pair 0 0) xs
    k (Pair n s) x = Pair (n+1) (s+x)

{-
main = do
  [d] <- map read `fmap` getArgs
  printf "%f\n" (mean [1..d])
-}

main = do
  print $ mean [1..1e7]
