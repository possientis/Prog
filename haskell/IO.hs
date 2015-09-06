import System.Directory

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

