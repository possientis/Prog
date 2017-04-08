sequenceIO :: [IO a] -> IO [a]
sequenceIO []     = return []
sequenceIO (a:as) = do
  x  <- a
  xs <- sequenceIO as
  return (x:xs)

l1 = [putStrLn "abc", putStrLn "def", putStrLn "ghi"]

main = do
  sequenceIO l1
  return ()
