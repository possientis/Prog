import System.IO

-- This program will work correctly on ghci
-- but not when compiled with ghc and linked
-- you need to disable output buffering
-- or use hFlush before each getLine

-- ain't gonna work with ghc
main1 :: IO ()
main1 = do
  putStr "What is your first name? "
  first <- getLine
  putStr "And your last name? "
  last <- getLine
  let full = first ++ " " ++ last
  putStrLn ("Pleased to meet you, " ++ full ++ "!")

-- disabling buffering
main2 :: IO ()
main2 = do
  hSetBuffering stdout NoBuffering
  putStr "What is your first name? "
  first <- getLine
  putStr "And your last name? "
  last <- getLine
  let full = first ++ " " ++ last
  putStrLn ("Pleased to meet you, " ++ full ++ "!")

-- usinf hFlush
main3 :: IO ()
main3 = do
  putStr "What is your first name? "
  hFlush stdout
  first <- getLine
  putStr "And your last name? "
  hFlush stdout
  last <- getLine
  let full = first ++ " " ++ last
  putStrLn ("Pleased to meet you, " ++ full ++ "!")

main :: IO ()
main = main3



