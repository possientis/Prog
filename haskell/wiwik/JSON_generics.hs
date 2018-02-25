{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

import Data.Text
import Data.Aeson
import GHC.Generics

import qualified Data.ByteString.Lazy.Char8 as BL

data Refs = Refs
    { a     :: Text
    , b     :: Text
    } deriving (Show,Generic,FromJSON,ToJSON)

data Data = Data
    { id    :: Int
    , name  :: Text
    , price :: Double
    , tags  :: [Text]
    , refs  :: Refs
    } deriving (Show,Generic,FromJSON,ToJSON)


main :: IO ()
main = do
    contents <- BL.readFile "example.json"
    let Just dat = decode contents
    print $ name dat
    print $ a (refs dat)
    BL.putStrLn $ encode dat
