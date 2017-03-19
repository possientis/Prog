
-- not tail-recursive
doubleList :: Num a => [a] -> [a]
doubleList []       = []
doubleList (n:ns)   = (2 * n) : doubleList ns 

{-
 - doubleList [1..5]  = 2 : doubleList [2..5]
 -                    = 2 : 4 : doubleList [3..5]
 -                    = 2 : 4 : 6 : doubleList [4..5]
 -                    = 2 : 4 : 6 : 8 : doubleList [5..5]
 -                    = 2 : 4 : 6 : 8 : 10 : doubleList []
 -                    = 2 : 4 : 6 : 8 : 10 : []
 -                    = 2 : 4 : 6 : 8 : [10]
 -                    = 2 : 4 : 6 : [8, 10]
 -                    = 2 : 4 : [6, 8, 10]
 -                    = 2 : [4, 6, 8, 10]
 -                    = [2, 4, 6, 8, 10]
 -}

-- This is a lot slower it seems
doubleList' :: Num a => [a] -> [a]
doubleList' xs = go (reverse xs) []
  where
  go [] ys      = ys
  go (x:xs) ys  = go xs ((2 * x) : ys)


main :: IO ()
main = do
  putStrLn  $ show $ length $ doubleList [1..5000000]
