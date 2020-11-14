data LR = L | R
    deriving (Show)

main :: IO ()
main = do
    print (decision 10000 pi)

tolerance :: Double
tolerance = 1e-7

decision :: Integer -> Double -> [LR]
decision n r = reverse (loop n r [])

loop :: Integer -> Double -> [LR] -> [LR]
loop n a lrs
    | n == 0    = lrs
    | equal a 1 = lrs
    | otherwise = let (a',lrs') = step a lrs
                  in loop (n - 1) a' lrs' 

step :: Double -> [LR] -> (Double, [LR])
step a lrs
    | a < 1     = (a/(1 - a), L : lrs) 
    | otherwise = (a - 1, R : lrs)

equal :: Double -> Double -> Bool
equal x y  = abs (x - y) < tolerance

data Matrix = Matrix
    { aMat :: Integer
    , bMat :: Integer
    , cMat :: Integer
    , dMat :: Integer
    }

instance Show Matrix where
    show m = "[(" ++ show (aMat m) ++ "," ++ show (bMat m) ++ "),(" 
           ++ show (cMat m) ++ "," ++ show (dMat m) ++ ")]"
prod :: Matrix -> Matrix -> Matrix
prod m1 m2 = Matrix
    { aMat = a1*a2 + b1*c2
    , bMat = a1*b2 + b1*d2
    , cMat = c1*a2 + d1*c2
    , dMat = c1*b2 + d1*d2
    }
    where
        a1 = aMat m1
        b1 = bMat m1
        c1 = cMat m1
        d1 = dMat m1
        a2 = aMat m2
        b2 = bMat m2
        c2 = cMat m2
        d2 = dMat m2

matrixI :: Matrix
matrixI  = Matrix 1 0 0 1

matrixL :: Matrix
matrixL  = Matrix 1 0 1 1

matrixR :: Matrix
matrixR  = Matrix 1 1 0 1

pow :: Integer -> Matrix -> Matrix
pow 0 m = matrixI
pow n m = prod m (pow (n - 1) m)

data Rat = Rat
    { numerator   :: Integer
    , denominator :: Integer
    } deriving (Eq)

instance Show Rat where
    show r = show (numerator r) ++ "/" ++ show (denominator r)

toRat :: Matrix -> Rat
toRat m = Rat (a + b) (c + d)
    where
        a = aMat m
        b = bMat m
        c = cMat m
        d = dMat m

toMatrix :: LR -> Matrix
toMatrix L = matrixL
toMatrix R = matrixR

scan :: [Matrix] -> [Matrix]
scan []     = []
scan (m:ms) = m : [ prod m x | x <- scan ms ]

approximate :: Integer -> Double -> [Rat]
approximate n r = map toRat $ scan $ map toMatrix $ decision n r

toRatio :: Rat -> Double
toRatio (Rat n m) = fromIntegral n / fromIntegral m

myMap :: (a -> b) -> [a] -> [b]
myMap f xs = [f x | x <- xs] 
