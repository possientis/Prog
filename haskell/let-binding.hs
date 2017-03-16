import Data.Char


main1 = do
  putStr "What is your name?"
  name <- getLine
  let loudName = makeLoud name
  putStrLn $ "Hello " ++ loudName ++ "!"
  putStrLn $ "Oh boy! Am I excited to see you, " ++ loudName



main2 = do
  putStr "What is your name?"
  name <- getLine
  let loudName = makeLoud name in do
    putStrLn $ "Hello " ++ loudName ++ "!"
    putStrLn $ "Oh boy! Am I excited to see you, " ++ loudName




makeLoud :: String -> String
makeLoud = map toUpper

