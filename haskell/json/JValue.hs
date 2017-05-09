module JValue 
  ( JValue(..)
  , JKeyVal(..)
  ) where


import Data.List (intercalate)
import Data.Char
import Control.Monad

newtype JKeyVal = JKeyVal (String, JValue) deriving (Eq)

instance Show JKeyVal where
  show (JKeyVal (k,v)) = (show k) ++ ": " ++ (serialize v) 

data JValue = JString String
            | JNumber Double
            | JBool Bool
            | JNull
            | JObject [JKeyVal]
            | JArray  [JValue]
            deriving (Eq)

instance Show JValue where show = serialize

serialize :: JValue -> String
serialize (JString s)   = show s
serialize (JNumber n)   = show n
serialize (JBool True)  = "true" 
serialize (JBool False) = "false" 
serialize (JNull)       = "null"
serialize (JObject kvs) = "{" ++ (intercalate ", " $ map show kvs) ++ "}"
serialize (JArray jvs)  = "[" ++ (intercalate ", " $ map serialize jvs) ++ "]"





