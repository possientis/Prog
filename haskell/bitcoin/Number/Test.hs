import Number

x = zero :: Number
y = one :: Number
z = fromInteger 23 :: Number
t = fromInteger $ -3 :: Number


main :: IO ()
main = do
  putStrLn $ "x = " ++ (show x)
  putStrLn $ "y = " ++ (show y)
  putStrLn $ "z = " ++ (show z)
  putStrLn $ "t = " ++ (show t)
  putStrLn $ " x == y : " ++ (show (x == y))
  putStrLn $ " x <= y : " ++ (show (x <= y))
  putStrLn $ "-x = " ++ (show $ negate x)
  putStrLn $ "-y = " ++ (show $ negate y)
  putStrLn $ "fromInteger 45 = " ++ (show $ fromInteger 45)
  putStrLn $ "z + t = " ++ (show $ z + t)
  putStrLn $ "z * t = " ++ (show $ z * t)
  putStrLn $ "signum z = " ++ (show $ signum z)
  putStrLn $ "signum t = " ++ (show $ signum t)
  putStrLn $ "signum x = " ++ (show $ signum x)
  putStrLn $ "toInteger z = " ++ (show $ toInteger z)
  


