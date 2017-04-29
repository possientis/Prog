{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}

class A a where
  toDouble :: a -> Double

instance A Double where
  toDouble = id

instance Integral a => A a where
  toDouble = fromIntegral

avg :: A a => [a] -> Double
avg xs = (sum $ map toDouble xs) / fromIntegral n
  where n = length xs





