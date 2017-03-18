import Prelude hiding (zip)

-- not tail recursive
zip' :: [a] -> [b] -> [(a,b)]
zip' []  ys        = []
zip' xs  []        = []
zip' (x:xs) (y:ys) = (x,y) : zip' xs ys


zip :: [a] -> [b] -> [(a,b)]
zip xs ys = reverse (go xs ys [])
  where
  go [] ys zs         = zs
  go xs [] zs         = zs
  go (x:xs) (y:ys) zs = go xs ys ((x,y):zs)


main :: IO ()
main = do
  putStrLn $ show (zip [1..5] [11..20])
