merge :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys)
  | x < y     = x:merge xs (y:ys)
  | otherwise = y:merge (x:xs) ys 

split :: [a] -> ([a],[a])
split []  = ([],[])
split [x] = ([x],[])
split (x:(y:xs)) = (x:u, y:v) where (u,v) = split xs 

mergeSort :: Ord a => [a] -> [a]
mergeSort []   = []
mergeSort [x]  = [x]
mergeSort xs = merge (mergeSort u) (mergeSort v) where (u,v) = split xs


