--import System.Directory

main :: IO ()
main = main2

main1 :: IO ()
main1 = do
  putStrLn "What is your name? (version 1)"
  name <- getLine
  putStrLn ("Nice to meet you, " ++ name ++ "!")

main2 :: IO ()
main2 =
  putStrLn "What is your name? (version 2)" >>
  getLine >>= \name ->
  putStrLn("Nice to meet you, " ++ name ++ "!")

f :: IO (Char,Char)
f = do
  x <- getChar
  _ <- getChar
  z <- getChar
  return (x,z)

g :: IO (Char,Char)
g = getChar >>= \x ->
      getChar >>= \_ ->
        getChar >>= \z ->
          return (x,z)

myGetLine :: IO String
myGetLine = do
  x <- getChar
  if x == '\n' then
    return []
  else
    do
      xs <- myGetLine
      return (x:xs)

myPutStr :: String -> IO ()
myPutStr [] = return ()
myPutStr (x:xs) = do
                  putChar x
                  myPutStr xs
myPutStrLn :: String -> IO ()
myPutStrLn xs = do myPutStr xs
                   putChar '\n'

strlen :: IO ()
strlen = do putStr "Enter a string: "
            xs <- getLine
            putStr "The string has "
            putStr (show (length xs))
            putStrLn " characters"

