{-# LANGUAGE FlexibleInstances #-} -- so we can make String an instance :(

module JSONclass(JSON, toJValue, fromJValue) where

import SimpleJSON



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


