streamSqrt :: Double -> [Double]
streamSqrt x = 1:map (\guess -> (guess + x/guess) * 0.5) (streamSqrt x)

piSummands :: Int -> [Double]
piSummands n = (1.0/fromIntegral n):map (\x -> -x) (piSummands (n + 2))

partialSum :: Num a => [a] -> [a]
partialSum [] = []
partialSum (x:xs) = x:map (\u -> u + x) (partialSum xs )

piStream :: [Double]
piStream = map (\x -> x * 4) (partialSum (piSummands 1))
