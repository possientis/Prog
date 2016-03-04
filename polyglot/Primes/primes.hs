import System.Environment -- getArgs

sieve :: [Int] -> [Int]
sieve (x:xs) = x:sieve [y | y <- xs, mod y x /= 0]

primes :: [Int]
primes = sieve [2..]

main :: IO ()
main = do
  [arg] <- getArgs
  putStrLn $ show (take (read arg :: Int) primes)



