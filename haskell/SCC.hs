-- adding SCC pragma for profiling
-- compile with -rtsopts to allow +RTS option
-- This allows you to increase stack size at run time
-- ./SCC +RTS -K1000000000

mean :: [Double] -> Double
mean xs = {-# SCC "mean" #-} sum xs /fromIntegral (length xs)


main = do 
  print $ mean [1..1e7]
