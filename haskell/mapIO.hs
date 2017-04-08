mapIO :: (a -> IO b) -> [a] -> IO [b]
mapIO f []      = return []
mapIO f (x:xs)  = do
  b   <- f x
  bs  <- mapIO f xs 
  return (b:bs)

l1 = ["abc", "def", "hij"]

main = do
  mapIO putStrLn l1
  return ()
