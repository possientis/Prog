fib = 1 : 1 : zipWith (+) fib (tail fib)



main = do
  putStrLn $ show $ take 20 fib


