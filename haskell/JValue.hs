module JValue 
  ( JValue(..)
  ) where

import Data.List (intercalate)
import Data.Char

newtype JKeyVal = JKeyVal (String, JValue)

instance Show JKeyVal where
  show (JKeyVal (k,v)) = (show k) ++ ": " ++ (serialize v) 

data JValue = JString String
            | JNumber Double
            | JBool Bool
            | JNull
            | JObject [JKeyVal]
            | JArray  [JValue]

instance Show JValue where show = serialize

serialize :: JValue -> String
serialize (JString s)   = show s
serialize (JNumber n)   = show n
serialize (JBool True)  = "true" 
serialize (JBool False) = "false" 
serialize (JNull)       = "null"
serialize (JObject o)   = "{" ++ (intercalate ", " $ map show o) ++ "}"
serialize (JArray a)    = "[" ++ (intercalate ", " $ map serialize a) ++ "]"



object1 = JObject [JKeyVal ("foo",JNumber 1),   JKeyVal ("bar", JBool False)]
object2 = JObject [JKeyVal ("foo",JNumber 3),   JKeyVal ("bar", JBool True)]
object3 = JObject [JKeyVal ("foo",JNumber 4.5), JKeyVal ("bar", JBool True)]
object4 = JArray [object1, object2, object3]

data Parser a = Parser { run :: String -> [(a, String)] }

parser :: (Char -> Bool) -> Parser String
parser p = Parser f where
  f []      = []
  f (c:cs)  = if p c then [([c],cs)] else []

item :: Parser String           -- "."
item = parser $ const True

char :: Char -> Parser String   -- "c"
char c = parser (== c)

digit :: Parser String          -- "[0-9]"
digit = parser isDigit 













main = do
  print object4
