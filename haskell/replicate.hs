import Prelude hiding (replicate)

-- not tail recursive
replicate' :: Int -> a -> [a]
replicate' 0 _ = []
replicate' n a = a : replicate' (n-1) a 

replicate :: Int -> a -> [a]
replicate n x = go n []
  where
  go 0 xs  = xs
  go n xs  = go (n-1) (x:xs) 


main :: IO ()
main = do
  putStrLn $ show (replicate 80 'a')

