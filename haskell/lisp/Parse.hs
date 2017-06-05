module Parse
  ( readExpr
  ) where

import Text.ParserCombinators.Parsec hiding (spaces)
import Control.Monad

import LispVal


symbol :: Parser Char
symbol = oneOf "!$%&|*+-/:<=?>@^_~#"

spaces :: Parser ()
spaces = skipMany1 space

parseEscapedChar :: Parser Char
parseEscapedChar = do
  char '\\'
  c <- char '"' <|> char '\\'
  return c

parseString :: Parser LispVal
parseString = do
  char '"'
  x <- many (noneOf "\"\\" <|> parseEscapedChar)
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
parseNumber = liftM (Number . read) $ many1 digit

parseExpr :: Parser LispVal
parseExpr = parseAtom <|> parseString <|> parseNumber

readExpr :: String -> String
readExpr input = case parse parseExpr "lisp" input of
  Left err    -> "No match: " ++ show err
  Right val   -> "Found Value: " ++ show val




