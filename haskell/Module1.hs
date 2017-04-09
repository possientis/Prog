module Module1 where

-- This will conflict with Module2
foo :: IO ()
foo = putStrLn "foo of Module1 is running"

-- This will not conflict with Module2
bar :: IO ()
bar = putStrLn "bar of Module1 is running"
