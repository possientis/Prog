
xs = [1..1000]            :: [Int]
p1 = even                 :: Int -> Bool
p2 = (<=15)               :: Int -> Bool 
f  = (\x -> x*x)          :: Int -> Int
ps = zip [1..20] [11..30] :: [(Int, Int)]

-- list comprehension is syntactic sugar:
as = [f x | x <- xs, p1 x, p2 x]

-- is the same as:
bs = map f $ filter (\x -> p1 x && p2 x) xs


cs = [f x | (x,y) <- ps, p1 y]
--
ds = map (f . fst) $ filter (\(x,y) -> p1 y) ps


allPairs1 = [(x,y) | x <- [1..4], y <- [5..8], x + y <= 10 ]

allPairs2 :: [(Int,Int)]
allPairs2 = do
  x <- [1..4]
  y <- [5..8]
  return (x,y)  -- hmmm what do i do here?


catMaybes :: [Maybe a] -> [a]
catMaybes xs = [ x | Just x <- xs ] -- nice !!


main :: IO ()
main = do
  putStrLn $ show as
  putStrLn $ show bs
  putStrLn $ show cs
  putStrLn $ show ds
  putStrLn $ show allPairs1
  putStrLn $ show allPairs2

