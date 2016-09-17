{-# LANGUAGE BangPatterns #-}

-- ghc F.hs -rtsopts (so as to allow RTS options)
-- ./F 1e7 +RTS -sstderr

-- enforced strictness allows computation is constant space. Only 2% of
-- running time now used by GC, leading to considerably faster code.

{-
In large projects, when we are investigating memory allocation hot spots, 
bang patterns are the cheapest way to speculatively modify the strictness 
properties of some code, as they’re syntactically less invasive than other 
methods.
-}

import System.Environment (getArgs)
import Data.List (foldl')
import Text.Printf (printf)

main = do
  [d] <- map read `fmap` getArgs
  printf "%f\n" (mean [1..d])

mean :: [Double] -> Double
mean xs = s /fromIntegral n
  where
    (n, s) = foldl' k (0,0) xs
    k (!n, !s) x = (n+1, s+x)   -- intermediate values are now strict


-- try1 is lazy by default, arguments are not
-- evaluated before execution of function's body
try1 :: Int -> Double -> Bool
try1 n m = if n == 0 then True else False


test1 = try1 0 undefined  -- this will compute without error


-- we now make the second argument strict. Hence it will be evaluated 
-- before the function's body. 
try2 :: Int -> Double -> Bool
try2 n !m = if n == 0 then True else False

test2 = try2 0 undefined  -- this will throw and exception



