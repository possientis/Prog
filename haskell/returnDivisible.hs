returnDivisible :: Int -> [Int] -> [Int]
returnDivisible n xs = [ x | x <- xs, x `mod` n == 0 ] 


main :: IO ()
main = do
  putStrLn $ show $ take 10 $ returnDivisible 13 [1..]
