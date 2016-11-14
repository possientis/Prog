qs :: (Ord a) => [a] ->[a]
qs [] = []
qs (x:xs) = qs smaller ++ [x] ++ qs larger where
  smaller = [y | y <- xs , y <= x]
  larger  = [y | y <- xs , y > x ]
  

