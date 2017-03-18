import Prelude hiding ((!!))

(!!) :: [a] -> Int -> a
[]     !! n  = error "(!!): index out of bound"
(x:xs) !! 0  = x  
(x:xs) !! n  = xs !! (n-1)


main :: IO ()
main = do
  putStrLn $ show ([1..5000] !! 399)
