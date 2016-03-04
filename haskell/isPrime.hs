-- need list of primes 'primes' to be defined 
isPrime :: Int -> Bool
isPrime n = (n > 1) && loop primes
  where loop (x:xs) | x*x > n       = True
                    | mod n x == 0  = False
                    | otherwise     = loop xs


