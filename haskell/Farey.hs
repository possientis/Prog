import Data.List

data Rat = Rat
    { numerator   :: Integer
    , denominator :: Integer
    } deriving (Eq)

instance Show Rat where
    show r = show (numerator r) ++ "/" ++ show (denominator r)

instance Ord Rat where
    r1 <= r2 = (numerator r1) * (denominator r2) <= (numerator r2) * (denominator r1)

farey :: Integer -> [Rat]
farey n
    | n <= 1    = [Rat 0 1, Rat 1 1]
    | otherwise = sort (previousFarey ++ new)
        where
            previousFarey :: [Rat]
            previousFarey = farey (n - 1)
            new :: [Rat]
            new = filter (\r -> denominator r == n)
                $ map mediant (consecutiveRat previousFarey)

mediant :: (Rat, Rat) -> Rat 
mediant (Rat a b, Rat c d) = Rat (a + c) (b + d)

consecutiveRat :: [Rat] -> [(Rat,Rat)]
consecutiveRat []  = []
consecutiveRat [x] = []
consecutiveRat (x:y:xs) = (x,y) : consecutiveRat (y:xs)
