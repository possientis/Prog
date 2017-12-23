import Test.QuickCheck

qsort :: [Int] -> [Int]
qsort []        = []
qsort (x:xs)    = qsort lhs ++ [x] ++ qsort rhs
    where   lhs = filter (< x)  xs
            rhs = filter (>= x) xs 


prop_maximum :: [Int] -> Property
prop_maximum xs = not (null xs) ==> last (qsort xs) == maximum xs

-- quickCheck :: Testable prop => prop -> IO ()
-- (==>) :: Testable prop => Bool -> prop -> Property
-- forAll :: (Show a, Testable prop) => Gen a => (a -> prop) -> Property
-- choose :: Random a => (a,a) -> Gen a


main :: IO ()
main = quickCheck prop_maximum


data Color = Red | Green | Blue deriving Show

instance Arbitrary Color where
    arbitrary = do
        n <- choose (0,2) :: Gen Int
        return $ case n of 
            0   -> Red
            1   -> Green
            2   -> Blue


example1 :: IO [Color]
example1 = sample' arbitrary
