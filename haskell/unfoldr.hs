import Data.List

f :: Int -> Maybe (Int,Int)
f 0 = Nothing
f x = Just (x,x-1)

rev :: [Int]
rev = unfoldr f 10


fibs :: [Int]
fibs = unfoldr (\(a,b) -> Just (a,(b,a+b))) (0,1)


main :: IO ()
main = do
    print $ take 20 fibs


