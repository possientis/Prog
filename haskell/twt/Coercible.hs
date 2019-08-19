{-# LANGUAGE FlexibleInstances  #-}

newtype Sum a = Sum { getSum :: a }

instance Monoid (Sum Int) where
    mempty = Sum 0
    mappend (Sum x)(Sum y) = Sum (x + y)

slowSum :: [Int] -> Int
slowSum = getSum . mconcat . fmap Sum
