{-# LANGUAGE OverloadedStrings #-}

import Data.Text as Text
import Data.ByteString
import Data.ByteString.Char8 as BS

withString :: String
withString = "Hello String"


withText :: Text
withText = "Hello Text"

withText' :: Text
withText' = Text.pack "Hello Text"

withBS :: ByteString
withBS = "Hello ByteString"

withBS' :: ByteString
withBS' = BS.pack "Hello ByteString"


main :: IO ()
main = do
    print withString
    print withText
    print withBS
