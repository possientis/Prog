main = do
  x <- getX
  putStrLn x  -- again


getX = do
  return "abc"
  return "def"
  return "ghi"
  return "again"
