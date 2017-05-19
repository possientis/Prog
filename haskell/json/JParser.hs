module JParser
  ( JParser
  , jparse
  ) where

import Parser
import JLexer
import JValue

import Control.Monad

type JParser = Parser JToken

jstring :: JParser JValue
jstring = Parser f where
  f []                  = []
  f ((TokString s):cs)  = [((JString s), cs)]
  f (_:cs)              = []
  
jnumber :: JParser JValue
jnumber = Parser f where
  f []                  = []
  f ((TokNumber d):cs)  = [((JNumber d), cs)]
  f (_:cs)              = []

jbool :: JParser JValue
jbool   = Parser f where
  f []                  = []
  f ((TokBool b):cs)    = [((JBool b), cs)]
  f (_:cs)              = []

jnull :: JParser JValue
jnull = liftM (\x -> JNull) (char TokNull)

jvalue  =   jstring 
        <|> jnumber 
        <|> jbool 
        <|> jnull 
        <|> jarray
        <|> jobject

jkeyval :: JParser JKeyVal
jkeyval = do
  (JString s) <- jstring
  colon       <- char TokColon
  value       <- jvalue
  return $ JKeyVal (s, value) 

-- TODO review design of jarray based on proper grammar
jarray_empty :: JParser JValue  
jarray_empty = liftM (\x-> JArray []) $ match [TokBracketL, TokBracketR]

jarray_single :: JParser JValue
jarray_single = do
  bracketl    <- char TokBracketL
  value       <- jvalue
  bracketr    <- char TokBracketR
  return $ JArray [value]

comma_jvalue :: JParser JValue
comma_jvalue  = do
  comma       <- char TokComma
  value       <- jvalue
  return value

jarray_many :: JParser JValue
jarray_many = do
  bracketl    <- char TokBracketL
  jvs         <- liftM (\(x,y) -> (x:y)) (jvalue &&& (plus comma_jvalue))
  bracketr    <- char TokBracketR 
  return $ JArray jvs

jarray :: JParser JValue
jarray = jarray_empty <|> jarray_single <|> jarray_many 


jobject_empty :: JParser JValue  
jobject_empty = liftM (\x-> JObject []) $ match [TokBraceL, TokBraceR]

jobject_single :: JParser JValue
jobject_single = do
  bracel      <- char TokBraceL
  keyval      <- jkeyval
  bracer      <- char TokBraceR
  return $ JObject [keyval]

comma_jkeyval :: JParser JKeyVal
comma_jkeyval  = do
  comma       <- char TokComma
  keyval      <- jkeyval
  return keyval

jobject_many :: JParser JValue
jobject_many = do
  bracel      <- char TokBraceL
  kvs         <- liftM (\(x,y) -> (x:y)) (jkeyval &&& (plus comma_jkeyval))
  bracketr    <- char TokBraceR 
  return $ JObject kvs

jobject :: JParser JValue
jobject = jobject_empty <|> jobject_single <|> jobject_many 

jparse :: String -> JValue
jparse cs = let 
  ts = run jflex cs 
  len = length ts in
    if len == 0
      then error "lexical analyser failed to recognize tokens"
      else if len > 1 
        then error "lexical analyser has ambiguous tokens"
        else let 
          tokens = fst $ head ts
          leftover = snd $ head ts in
            if leftover /= ""
              then error "lexical analyser failed to analyse full string"
              else let
                jvs = run jvalue tokens
                len' = length jvs in
                  if len' == 0
                    then error "parser failed to parse token stream"  
                    else if len' > 1
                      then error "parser cannot disambiguate token stream"
                      else let
                        value = fst $ head jvs
                        leftover' = snd $ head jvs in
                            if leftover' /= []
                              then error "parser failed to analyse all tokens"
                              else value
    
