import Test.QuickCheck

prop_times2even :: Integer -> Bool
prop_times2even n = even (2 * n)


prop_evenplus1 :: Integer -> Property
prop_evenplus1 n = even n ==> odd (n + 1)


prop_length_reverse :: [a] -> Bool
prop_length_reverse xs = length xs == length (reverse xs)


main :: IO ()
main = do
    quickCheck prop_times2even 
    quickCheck prop_evenplus1
    quickCheck prop_length_reverse
