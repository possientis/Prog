module Parse
  ( check
  , hexChar
  , hexNumber
  , readExpr
  , spaces
  , symbol
  ) where

import Text.ParserCombinators.Parsec hiding (spaces)
import Control.Monad
import Numeric

import LispVal


symbol :: Parser Char
symbol = oneOf "!$%&|*+-/:<=?>@^_~#"

spaces :: Parser ()
spaces = skipMany1 space

hexChar :: Parser Char
hexChar = digit <|> oneOf "abcdefABCDEF"

hexNumber :: Parser Integer
hexNumber = do
  char '#'
  char 'x'
  s <- many1 hexChar 
  let list = readHex s
  return $ (fst . head) list

octChar :: Parser Char
octChar = oneOf "01234567"

binChar :: Parser Char
binChar = char '0' <|> char '1'

decChar :: Parser Char
decChar = digit

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
parseNumber = liftM Number hexNumber

parseExpr :: Parser LispVal
parseExpr = parseNumber <|> parseAtom <|> parseString

readExpr :: String -> String
readExpr input = case parse parseExpr "lisp" input of
  Left err    -> "No match: " ++ show err
  Right val   -> "Found Value: " ++ show val

check :: Parser a -> String -> Maybe a
check parser input = case parse parser "lisp" input of
  Left err    -> Nothing
  Right val   -> Just val




