{-# LANGUAGE BangPatterns   #-}
module Main (main) where

import Debug.Trace

-- $ ./Sum +RTS -s

main :: IO ()
main = print $ sum5 [1..10000000]

-- space leak: not tail recursive
sum1 :: [Int] -> Int
sum1 []     = 0
sum1 (x:xs) = x + sum1 xs

-- still space leak: tail recursive but nothing forcing 'acc + x'
sum2 :: [Int]-> Int
sum2 xs = go 0 xs where
    go acc []     = acc
    go acc (x:xs) = go (acc + x) xs


-- no space leak: tail recursive, forcing 'acc + x'
-- and not obvious but it seems 'sharing' must be happening
sum3 :: [Int] -> Int
sum3 xs = go 0 xs where
    go acc []     = acc
    go acc (x:xs) = seq (acc + x) $ go (acc + x) xs

-- no space leak: tail recursive, forcing and making sharing obvious
sum4 :: [Int] -> Int
sum4 xs = go 0 xs where
    go acc []     = acc
    go acc (x:xs) = let y = acc + x in seq y $ go y xs

-- better syntax, making argument 'acc' strict
sum5 :: [Int]-> Int
sum5 xs = go 0 xs where
    go !acc []     = acc
    go !acc (x:xs) = go (acc + x) xs
