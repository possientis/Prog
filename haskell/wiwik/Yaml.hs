{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

import Data.Text
import Data.Yaml
import GHC.Generics
import qualified Data.ByteString as BL

data Invoice = Invoice
    { invoice   :: Int
    , date      :: Text
    , bill      :: Billing
    } deriving (Show,Generic,FromJSON) 


data Billing = Billing 
    { address   :: Address
    , family    :: Text
    , given     :: Text
    } deriving (Show,Generic,FromJSON)

data Address = Address
    { lines     :: Text
    , city      :: Text
    , state     :: Text
    , postal    :: Int
    } deriving (Show,Generic,FromJSON)


main :: IO ()
main = do
    contents <- BL.readFile "example.yaml"
    let res = decodeEither contents :: Either String Invoice
    case res of
        Right val   -> print val
        Left  err   -> putStrLn err
