pascal :: Int -> [Int]
pascal 1 = [1]
pascal n = addList (shiftLeft (pascal (n - 1)))
                   (shiftRight(pascal (n - 1)))

shiftLeft :: [Int] -> [Int]
shiftLeft xs = xs ++ [0]

shiftRight :: [Int] -> [Int]
shiftRight xs = 0:xs

addList :: [Int] -> [Int] -> [Int]
addList xs ys = zipWith (+) xs ys

fastPascal :: Int -> [Int]
fastPascal 1 = [1]
fastPascal n = let seq = fastPascal (n - 1)
  in addList (shiftLeft seq) (shiftRight seq)

main = putStrLn $ show (fastPascal 20)
