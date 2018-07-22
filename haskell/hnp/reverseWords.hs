reverseWords :: String -> [String]
reverseWords = reverse . words


main :: IO ()
main = do
    content <- readFile "loremipsum.txt"
    mapM_ putStrLn $ reverseWords content
