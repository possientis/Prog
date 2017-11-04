nodups :: (Eq a) => [a] -> [a]
nodups []                   = []
nodups [x]                  = [x]
nodups (y:x:xs) | y == x    = nodups (x:xs)
nodups (y:x:xs)             = y : nodups (x:xs) 



main :: IO ()
main = do
    putStrLn $ show $ nodups [1::Int,2,2,3,4,4,4,5,5,6,7,7,7,7,8,9,0,0,0]
