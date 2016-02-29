sieve :: [Int] -> [Int]
sieve (x:xs) = x:sieve [y | y <- xs, mod y x /= 0]

primes :: [Int]
primes = sieve [2..]

main = putStrLn $ show (take 1000 primes)

isPrime :: Int -> Bool
isPrime n = (n > 1) && loop primes
  where loop (x:xs) | x*x > n       = True
                    | mod n x == 0  = False
                    | otherwise     = loop xs


