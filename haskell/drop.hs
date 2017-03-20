import Prelude hiding (drop)


drop :: Int -> [a] -> [a]
drop 0 xs     = xs
drop n []     = []
drop n (x:xs) = drop (n-1) xs


main :: IO ()
main = do
  putStrLn $ show $ drop 5 [1..10]
