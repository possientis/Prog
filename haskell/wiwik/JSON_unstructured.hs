{-# LANGUAGE OverloadedStrings #-}

import Data.Text
import Data.Aeson
import Data.Vector
import qualified Data.ByteString.Lazy as BL
import qualified Data.HashMap.Strict as M

-- pull a key out of a JSON object
(^?) :: Value -> Text -> Maybe Value
(^?) (Object obj) k = M.lookup k obj
(^?) _ _            = Nothing

-- pull the ithvalue out of a JSON list
ix :: Value -> Int -> Maybe Value 
ix (Array arr) i    = arr !? i
ix _ _              = Nothing

readJSON :: BL.ByteString -> Maybe (Value, Value, Value)
readJSON str = do
    obj     <- decode str :: Maybe Value
    price   <- obj ^? "price"
    refs    <- obj ^? "refs"
    tags    <- obj ^? "tags"
    aref    <- refs ^? "a"
    tag1    <- tags `ix` 0
    return (price,aref,tag1) 


main :: IO ()
main = do
    contents <- BL.readFile "example.json"
    print $ readJSON contents
-- Just (Number 12.5,String "red",String "home")

 
