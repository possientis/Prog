streamSqrt :: Double -> [Double]
streamSqrt x = 1:map (\guess -> (guess + x/guess) * 0.5) (streamSqrt x)

piSummands :: Int -> [Double]
piSummands n = (1.0/fromIntegral n):map (\x -> -x) (piSummands (n + 2))

partialSum :: Num a => [a] -> [a]
partialSum [] = []
partialSum (x:xs) = x:map (\u -> u + x) (partialSum xs )

piStream :: [Double]
piStream = map (\x -> x * 4) (partialSum (piSummands 1))

square :: Num a => a -> a
square x = x*x

eulerTransform :: [Double] -> [Double]
eulerTransform (x0:x1:x2:xs) = (x2 - (square (x2 - x1))/(x0 - 2*x1 + x2)):ys where
  ys = eulerTransform (x1:x2:xs)

piStream2 :: [Double]
piStream2 = eulerTransform piStream

makeTableau :: ([Double] -> [Double]) -> [Double] -> [[Double]]
makeTableau f xs = xs:makeTableau f (f xs)

accelerate :: ([Double] -> [Double]) -> [Double] -> [Double]
accelerate f xs = map head (makeTableau f xs) 

piStream3 :: [Double]
piStream3 = accelerate eulerTransform piStream
