module Specialize (spec, nonspec, f) where

{-# SPECIALIZE INLINE f :: Double -> Double -> Double #-}

f :: Floating a => a -> a -> a
f x y = exp (x + y) * exp (x + y)


nonspec :: Float
nonspec = f 10 20

spec :: Double
spec = f 10 20


