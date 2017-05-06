process :: Eq a => [a] -> [a]
process xs  = concatMap (\(x,n) -> replicate n x) (count_sort xs)

-- foldr :: (a -> b -> b) -> b -> [a] -> b

add :: Eq a => a -> [(a,Int)] -> [(a,Int)]
add x []          = [(x,1)]
add x ((y,n):ps) | (x == y) = (y,n+1):ps
add x ((y,n):ps) | (x /= y) = (y,n):(add x ps)

count :: Eq a => [a] -> [(a,Int)]
count = foldr add []

list1 = [0,1,2,0,4,1,2,4,5,8,9,2,3,1,1,0,6,7,3,3,3] :: [Int]

sort :: Ord a => [a] -> [a]
sort []   = []
sort (x:xs) = sort [u | u <- xs, u < x] ++ [x] ++ sort [u | u <- xs, u >= x]

data Wrapped a = Wrapped { unwrap :: (a , Int) } deriving Eq

instance Eq a => Ord (Wrapped a) where
  x <= y = snd (unwrap x) <= snd (unwrap y)

count_sort :: Eq a => [a] -> [(a, Int)]
count_sort xs = map unwrap (sort $ map Wrapped (count xs))

main = do
  putStrLn $ "list1 = " ++ (show list1)
  putStrLn $ "count list1 = " ++ (show $ count list1)
  putStrLn $ "count_sort list1 = " ++ (show $ count_sort list1)
  putStrLn $ "process list1 = " ++ (show $ process list1)


