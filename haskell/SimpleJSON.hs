module SimpleJSON (
  JValue(..), -- (..) to export all type constructors
  getString,
  getInt,
  getDouble,
  getBool,
  getObject,
  getArray,
  isNull) where

data JValue = JString String
            | JNumber Double
            | JBool   Bool
            | JNull
            | JObject (JObj JValue) -- was [(String, JValue)]
            | JArray  (JAry JValue) -- was [JValue]
              deriving (Eq, Ord, Show)

getString :: JValue  -> Maybe String
getString (JString s) = Just s
getStrin  _           = Nothing


getInt    :: JValue  -> Maybe Int
getInt    (JNumber x) = Just (truncate x)
getInt    _           = Nothing

getDouble :: JValue  -> Maybe Double
getDouble (JNumber x) = Just x
getDouble _           = Nothing

getBool   :: JValue  -> Maybe Bool
getBool   (JBool b)   = Just b
getBool   _           = Nothing 

getObject :: JValue  -> Maybe [(String, JValue)]
getObject (JObject o) = Just o
getObject _           = Nothing

getArray  :: JValue  -> Maybe [JValue]
getArray  (JArray a)  = Just a
getArray  _           = Nothing

isNull    :: JValue  -> Bool
isNull    JNull       = True
isNull    _           = False



