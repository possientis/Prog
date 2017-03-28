factList :: Integer -> [Integer]
factList n = scanl1 (*) [1..n]


