import Data.List (permutations)
import Test.QuickCheck

longRunningFunction :: [a] -> Int
longRunningFunction xs = length (permutations xs)

factorial :: Integral a => a -> a
factorial n = product [1..n]

prop_numberOfPermutations :: [Integer] -> Bool
prop_numberOfPermutations xs = longRunningFunction xs == factorial (length xs)


main :: IO ()
main = do
    quickCheckWith (stdArgs { maxSize = 10}) prop_numberOfPermutations


