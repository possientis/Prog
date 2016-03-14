d1 = [Just 5, Nothing, Nothing, Just 8, Just 9]::[Maybe Int]


main = do
  writeFile "log" (show d1)
  input <- readFile "log" 
  let d2 = (read input)::[Maybe Int]
    in putStrLn (show d2)


