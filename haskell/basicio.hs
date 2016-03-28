action = putStrLn "Hello, world!"
action2 = action

main = do
  putStrLn "Greetings! What is your name?"
  inpStr <- getLine
  putStrLn $ "Welcome to Haskell, " ++ inpStr ++ "!"

main' = 
  putStrLn "Greetings! What is your name?" >>
  getLine >>= 
  (\inpStr -> putStrLn $ "Welcome to Haskell, " ++ inpStr ++ "!")
