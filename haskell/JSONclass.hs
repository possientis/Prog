{-# LANGUAGE FlexibleInstances #-} -- so we can make String an instance :(

module JSONclass(JSON, toJValue, fromJValue) where

import SimpleJSON
import Control.Arrow(second)

newtype JAry a = JAry {
  fromJAry :: [a]
} deriving (Eq, Ord, Show)

newtype JObj a = JObj {
  fromJObj :: [(String,a)]
} deriving (Eq, Ord, Show)



type JSONError = String

class JSON a where
  toJValue :: a -> JValue
  fromJValue :: JValue -> Either JSONError a


instance JSON JValue where
  toJValue = id
  fromJValue = Right

instance JSON Bool where
  toJValue = JBool
  fromJValue (JBool b) = Right b
  fromJValue _         = Left "fromJValue: argument is not a JSON boolean"


instance JSON String where
  toJValue = JString
  fromJValue (JString s) = Right s
  fromJValue _           = Left "fromJValue: argument is not a JSON string"


instance JSON Double where
  toJValue = JNumber
  fromJValue (JNumber x) = Right x
  fromJValue _           = Left "fromJValue: argument is not a JSON double"

instance JSON Int where
  toJValue = JNumber . realToFrac
  fromJValue (JNumber x) = Right (round x)
  fromJValue _           = Left "fromJValue: argument is not a JSON integer"

instance JSON Integer where
  toJValue = JNumber . realToFrac
  fromJValue (JNumber x) = Right (round x)
  fromJValue _           = Left "fromJValue: argument is not a JSON integer"

jaryFromJValue :: (JSON a) => JValue -> Either JSONError (JAry a)
jaryFromJValue (JArray (JAry a)) =
  whenRight JAry (MapEithers fromJValue a)
jaryFromJValue _ = Left "fromJValue: argument is not a JSON array"

whenRight :: (b -> c) -> Either a b -> Either a c
whenRight _ (Left err) = Left err
whenRight f (Right a) = Right (f a)


mapEithers :: (a -> Either b c) -> [a] -> Either b [c]
mapEithers f (x:xs) = case mapEithers f xs of
                        Left err -> Left err
                        Right ys -> case f x of
                                      Left err -> Left err
                                      Right y -> Right (y:ys)
mapEithers _ _ = Right []




jaryToJValue    :: (JSON a) => JAry a -> JValue
jaryToJValue = JArray . JAry . map toJValue . fromJAry

instance (JSON a) => JSON (JAry a) where
  toJValue = jaryToJValue
  fromJValue = jaryFromJValue

listToJValues :: (JSON a) => [a] -> [JValue]
listToJValues = map toJValue

jvaluesToJAry :: [JValue] -> JAry JValue
jvaluesToJary = JAry

jaryOfJValuesToJValue :: JAry JValue -> JValue
jaryOfJValuesToJValue = JArray 


instance (JSON a) => JSON (JObj a) where
  toJValue = JObject . JObj . map (second toJValue) . fromJObj
  fromJValue (JObject (JObj o)) = whenRight JObj (mapEithers unwrap o)
    where unwrap (k,v) = whenRight ((,) k) (fromJValue v)
  fromJValue _ = Left "not a JSON object"





