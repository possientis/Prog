import System.Environment -- getArgs
import Data.List  -- intercalate

sieve :: [Int] -> [Int]
sieve (x:xs) = x:sieve [y | y <- xs, mod y x /= 0]

primes :: [Int]
primes = sieve [2..]

main :: IO ()
main = do
  [arg] <- getArgs
  let numPrimes = read arg ::Int in
    putStrLn $ "(" ++ 
                intercalate " " (map show (take numPrimes primes))
                ++ ")"



