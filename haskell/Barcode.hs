

mapEveryOther :: (a -> a) -> [a] -> [a]
mapEveryOther f = zipWith ($) (cycle [f,id])

test0 = mapEveryOther (\x -> x * x) [2,3,4,5,6,7,8,9,10]  -- [4,3,16,5,36,7,64,9,100]
