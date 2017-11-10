import Data.List.Split

example1 :: [String]
example1 = splitOn "." "foo.bar.baz"


example2 :: [String]
example2 = chunksOf 10 "too be or not to be that is the question"




main :: IO ()
main = do
    print example1
    print example2



