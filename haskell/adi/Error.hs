{-# LANGUAGE GeneralizedNewtypeDeriving     #-}

module  Error
    (   Error
    ,   mkError
    ,   printTrace
    )   where


newtype Error = Error { unError :: [String] }
    deriving (Semigroup, Monoid, Show)

mkError :: String -> Error
mkError s = Error [s]

printTrace :: Error -> IO ()
printTrace e = mapM_ putStrLn $ unError e

