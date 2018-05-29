{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

class IsString a where
    fromString :: String -> a


instance IsString String where
    fromString xs = xs



main :: IO ()
main = do
    putStrLn $ show $ (fromString "foo"  :: String )
