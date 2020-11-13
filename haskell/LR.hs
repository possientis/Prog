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


