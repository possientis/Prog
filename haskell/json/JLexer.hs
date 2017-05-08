module JLexer
  ( JLexer
  , JToken(..)
  , jbool
  , jbracel
  , jbracer
  , jbracketl
  , jbracketr
  , jcolon
  , jcomma
  , jflex
  , jnull
  , jnumber
  , jspace
  , jstring
  , jtoken
  ) where

import Parser
import JNumber

import Control.Monad


type JLexer = Parser Char

data JToken
  = TokString String 
  | TokNumber Double
  | TokBool Bool
  | TokNull
  | TokBraceL
  | TokBraceR
  | TokBracketL
  | TokBracketR
  | TokColon
  | TokComma
  | TokSpace
  deriving (Show)


string :: JLexer String
string = do
  s1 <- char '\"'
  s2 <- star' (predicate (/= '\"')) 
  s3 <- char '\"'
  return s2

bool :: JLexer Bool
bool  = liftM (\s -> if s == "true" then True else False) $
  match "true" +++ match "false"

jstring :: JLexer JToken
jstring = liftM TokString string

jnumber :: JLexer JToken
jnumber = liftM TokNumber number 

jbool :: JLexer JToken
jbool = liftM TokBool bool

jnull :: JLexer JToken
jnull = liftM (const TokNull) (match "null")

jbracel :: JLexer JToken
jbracel = liftM (const TokBraceL) (char '{')

jbracer :: JLexer JToken
jbracer = liftM (const TokBraceR) (char '}')

jbracketl :: JLexer JToken
jbracketl = liftM (const TokBracketL) (char '[')

jbracketr :: JLexer JToken
jbracketr = liftM (const TokBracketR) (char ']')

jcolon :: JLexer JToken
jcolon = liftM (const TokColon) (char ':')

jcomma :: JLexer JToken
jcomma = liftM (const TokComma) (char ',')

jspace :: JLexer JToken
jspace = greed $ liftM (const TokSpace) ((plus' . range) " \t\n")

jtoken :: JLexer JToken
jtoken  =   jstring
        +++ jnumber
        +++ jbool
        +++ jnull
        +++ jbracel
        +++ jbracer
        +++ jbracketl
        +++ jbracketr
        +++ jcolon
        +++ jcomma 
        +++ jspace

jflex :: JLexer [JToken]
jflex = (greed . plus) jtoken




