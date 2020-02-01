type Way = [Int]

ways :: Int -> [Int] -> [Way]
ways _ [] = []
ways n (x : xs) = concatMap process [1..(n `div` x)] ++ ways n xs  
    where
    process k 
        | n - k * x >= 1 = map ((replicate k x) ++) $ ways (n - k * x) xs
        | otherwise      = [replicate k x]


