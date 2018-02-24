{-# LANGUAGE DeriveGeneric #-}

import Data.Text
import Data.Aeson
import GHC.Generics

import qualified Data.ByteString.Lazy as BL

data Refs = Refs
    { a :: Text
    , b :: Text
    } deriving (Show, Generic)

data Data = Data
    { id    :: Int
    , name  :: Text
    , price :: Double
    , tags  :: [Text]
    , refs  :: Refs
    } deriving (Show, Generic)


instance FromJSON Data
instance FromJSON Refs
instance ToJSON Data
instance ToJSON Refs


-- data Result a = Error String | Success a

test1 = fromJSON (Bool True) :: Result Bool
test2 = fromJSON (Bool True) :: Result Double

main :: IO ()
main = do
    contents <- BL.readFile "example.json"
    let Just dat = decode contents
    print $ name dat
    print $ a (refs dat)
    print test1
    print test2
-- "A green door"
-- "red"
-- Success True
-- Error "expected Double, encountered Boolean"







