{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}

import Data.Kind

type family StringOrInt (t :: Bool) :: Type where
    StringOrInt 'False = String
    StringOrInt 'True  = Int

class GetStringOrInt (a :: Bool) where
    getStringOrInt :: StringOrInt a

instance GetStringOrInt 'False where
    getStringOrInt = "Ninety four"

instance GetStringOrInt 'True where
    getStringOrInt = 94

main :: IO ()
main = do
    putStr "Input a boolean value: "
    s <- getLine
    let b = if s == "True" then True else False
    return ()
