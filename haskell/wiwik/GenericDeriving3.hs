{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

import Data.Aeson
import GHC.Generics (Generic)
import Data.ByteString.Lazy

data Point = Point { _x :: Double, _y :: Double }
    deriving (Generic, Show)

instance FromJSON Point
instance ToJSON Point


ex1 :: Maybe Point
ex1 = decode "{\"_x\":3.0,\"_y\":-1.0}"
-- Just (Point {_x = 3.0, _y = -1.0})

ex2 :: ByteString
ex2 = encode $ Point 123.4 20
-- "{\"_y\":20,\"_x\":123.4}"


