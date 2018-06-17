{-# LANGUAGE RankNTypes #-}

foo :: (forall a. a -> String) -> String -> Int -> IO ()
foo show' string int = do
    putStrLn (show' string)
    putStrLn (show' int)


