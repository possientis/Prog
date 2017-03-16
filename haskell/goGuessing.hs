
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
