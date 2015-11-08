sieve :: [Int] -> [Int]
sieve (x:xs) = x:sieve [y | y <- xs, mod y x /= 0]

primes :: [Int]
primes = sieve [2..]

main = putStrLn $ show (take 500 primes)
