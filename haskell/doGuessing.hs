
doGuessing :: Integer -> IO ()
doGuessing num = do
  putStrLn "Enter your guess:"
  guess <- getLine
  if read guess < num
    then do putStrLn "Too low!"
            doGuessing num
    else if read guess > num
            then do putStrLn "too high!"
                    doGuessing num
            else putStrLn "You win!"

doGuessing' :: Integer -> IO ()
doGuessing' num = do
  putStrLn "Enter your guess:"
  guess <- getLine
  case compare (read guess) num of
    LT  -> do putStrLn  "Too low!"
              doGuessing' num
    GT  -> do putStrLn "Too high!"
              doGuessing' num 
    EQ  -> do putStrLn "You win!"
