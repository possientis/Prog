main :: IO ()
main = do
  putStrLn "The Base?"
  base <- read <$> getLine :: IO Double
  putStrLn "The height?"
  height <- read <$> getLine :: IO Double
  let area = 0.5 * base * height
  putStrLn $ "The area of the triangle is " ++ (show area)
