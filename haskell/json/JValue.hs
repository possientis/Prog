module JValue 
  ( JValue(..)
  ) where

import JLexer
import Parser -- TODO: remove this dependency

import Data.List (intercalate)
import Data.Char
import Control.Monad


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

main = do 
  print $ run jtoken "\"this is a string\"abcdef"
  print $ run jtoken "-4.576abcdef"
  print $ run jtoken "trueabcdef"
  print $ run jtoken "falseabcdef"
  print $ run jtoken "nullabcdef"
  print $ run jtoken "{abcdef"
  print $ run jtoken "}abcdef"
  print $ run jtoken "[abcdef"
  print $ run jtoken "]abcdef"
  print $ run jtoken ":abcdef"
  print $ run jtoken ",abcdef"
  print $ run jtoken " abcdef"
  print $ run jtoken "  abcdef"
  print $ run jtoken "\t \n \t    \t  \nabcdef"
  print $ run jflex  (show object1)
  print $ run jflex  (show object2)
  print $ run jflex  (show object3)
  print $ run jflex  (show object4)



