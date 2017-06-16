module Parse
  ( binChar 
  , binNumber
  , check
  , decNumber
  , hexChar
  , hexNumber
  , octChar
  , octNumber
  , parseChar
  , parseNumber
  , readExpr
  , spaces
  , symbol
  ) where

import Data.Char
import Control.Monad
import Text.ParserCombinators.Parsec hiding (spaces)
import Numeric

import LispVal


symbol :: Parser Char
symbol = oneOf "!$%&|*+-/:<=?>@^_~#"

spaces :: Parser ()
spaces = skipMany1 space

hexChar :: Parser Char
hexChar = digit <|> oneOf "abcdefABCDEF"

octChar :: Parser Char
octChar = oneOf "01234567"

binChar :: Parser Char
binChar = char '0' <|> char '1'

hexNumber :: Parser Integer
hexNumber = do 
  try $ char '#' >> char 'x'
  s <- many1 hexChar 
  let list = readHex s
  return $ (fst . head) list

octNumber :: Parser Integer
octNumber = do
  try $ char '#' >> char 'o'
  s <- many1 octChar 
  let list = readOct s
  return $ (fst . head) list

readBinary :: String -> Integer
readBinary [] = error "readBinary: no number to read"
readBinary xs = go xs 0 where
  go [] acc     = acc
  go (x:xs) acc = case x of 
    '0'       -> go xs (2*acc)
    '1'       -> go xs (2*acc + 1)
    otherwise -> error "readBinary: illegal character"

binNumber :: Parser Integer
binNumber = do
  try $ char '#' >> char 'b'
  s <- many1 binChar 
  return $ readBinary s

decNumber :: Parser Integer
decNumber = 
  ( do
      try $ char '#' >> char 'd'
      s <- many1 digit
      return $ read s
  ) 

number :: Parser Integer
number = liftM read $ many1 digit


escaped :: Parser Char
escaped = do
  char '\\'
  c <-  char '"' 
    <|> char '\\' 
    <|> char 'n'
    <|> char 't'
    <|> char 'r'
  return $ case c of
    '"'   ->  '"'
    '\\'  ->  '\\'
    'n'   ->  '\n'
    't'   ->  '\t'
    'r'   ->  '\r'

simpleChar :: Parser Char
simpleChar = do
  try $ char '#' >> char '\\'
  s <- oneOf "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
    <|> digit
    <|> symbol
    <|> oneOf "`'\"();\\,."
  return s

octalChar :: Parser Char
octalChar = do
  try $ char '#' >> char '\\'
  s <- many1 octChar 
  let list = readOct s
  return $ intToDigit $ (fst . head) list


parseChar :: Parser LispVal
parseChar = liftM Char (simpleChar <|> octalChar)
  

parseString :: Parser LispVal
parseString = do
  char '"'
  x <- many (noneOf "\"\\" <|> escaped)
  char '"'
  return $ String x 


parseAtom :: Parser LispVal
parseAtom = do
  first <- letter <|> symbol
  rest  <- many (letter <|> digit <|> symbol)
  let atom = [first] ++ rest 
  return $ case atom of
    "#t"      -> Bool True
    "#f"      -> Bool False
    otherwise -> Atom atom


parseNumber :: Parser LispVal
parseNumber = liftM Number $ 
    ( number 
  <|> decNumber 
  <|> hexNumber 
  <|> binNumber
  <|> octNumber
    )

parseExpr :: Parser LispVal
parseExpr = parseNumber <|> parseAtom <|> parseString <|> parseChar

readExpr :: String -> String
readExpr input = case parse parseExpr "lisp" input of
  Left err    -> "No match: " ++ show err
  Right val   -> "Found Value: " ++ show val

check :: Parser a -> String -> Maybe a
check parser input = case parse parser "lisp" input of
  Left err    -> Nothing
  Right val   -> Just val




