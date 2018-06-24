{-# LANGUAGE RankNTypes #-}

foo :: (forall a. Show a => a -> String) -> String -> Int -> IO ()
foo show' string int = do
    putStrLn (show' string)
    putStrLn (show' int)



main :: IO ()
main = do
    foo show "Hello" 43


