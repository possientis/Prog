name2reply :: String -> String
name2reply name =
  "Pleased to meet you, " ++ name ++ ".\n" ++
  "Your name contains " ++ charcount ++ " characters."
  where charcount = show (length name)

main :: IO ()
main = do
  putStrLn "Greetings once again. What is your name?"
  inpStr <- getLine -- <- to extract value from action
  let outStr = name2reply inpStr -- 'let' to extract value from pure code: no 'in' after 'let' in a 'do' block
  putStrLn outStr
