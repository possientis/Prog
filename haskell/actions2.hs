str2message :: String -> String
str2message input = "Data: " ++ input

str2action :: String -> IO ()
str2action = putStrLn . str2message

numbers :: [Int]
numbers = [1..10]

main = do
  str2action "Start of the program"
  mapM_ (str2action . show) numbers -- 'map' is pure, need mapM or mapM_
  str2action "Done!"
  


-- :t mapM_ , mapM_ :: Monad m => (a -> m b) -> [a] -> m ()
-- :t mapM  , mapM :: Monad m => (a -> m b) -> [a] -> m [b]
-- :t (>>)  , (>>) :: Monad m => m a -> m b -> m b
-- :t (>>=) , (>>=) :: Monad m => m a -> (a -> m b) -> m b
