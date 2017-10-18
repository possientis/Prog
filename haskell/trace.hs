import Debug.Trace

example1 :: Int
example1 = trace "impure print" 1

example2 :: Int
example2 = traceShow "impure print" 2

example3 :: [Int]
example3 = [trace "will not be called" 3]


main :: IO ()
main = do
    print example1
    print example2
    print $ length example3
