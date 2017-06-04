{-# LANGUAGE FlexibleContexts #-}

import Control.Monad
import Control.Monad.Identity
import System.Environment (getArgs)
import Text.Parsec hiding (spaces)
import System.IO

import LispVal


symbol :: Stream s m Char => ParsecT s u m Char
symbol = oneOf "!#$%&|*+-/:<=>?@^_~"

spaces :: Stream s m Char => ParsecT s u m ()
spaces = skipMany1 space

strChar :: Stream s m Char => ParsecT s u m Char
strChar = (noneOf "\\\"") <|> 
          (char '\\' >> char '"') <|>
          (char '\\' >> char '\\')

parseString :: Stream s m Char => ParsecT s u m LispVal
parseString = do 
  char '"'
  x <- many strChar
  char '"'
  return $ String x

parseAtom :: Stream s m Char => ParsecT s u m LispVal
parseAtom = do 
  first <- letter <|> symbol
  rest  <- many (letter <|> digit <|> symbol)
  let atom = [first] ++ rest
  return $ case atom of
    "#t"      -> Bool True
    "#f"      -> Bool False
    otherwise -> Atom atom

parseNumber :: Stream s m Char => ParsecT s u m LispVal
parseNumber = (Number . read) <$> many1 digit

parseList :: Stream s m Char => ParsecT s u m LispVal
parseList = liftM List $ sepBy parseExpr spaces

parseDottedList :: Stream s m Char => ParsecT s u m LispVal
parseDottedList = do
  head <- endBy parseExpr spaces
  tail <- char '.' >> spaces >> parseExpr
  return $ DottedList head tail

parseQuoted :: Stream s m Char => ParsecT s u m LispVal
parseQuoted = do
  char '\''
  x <- parseExpr
  return $ List [Atom "quote", x]

parseExpr :: Stream s m Char => ParsecT s u m LispVal
parseExpr   = parseAtom 
          <|> parseString 
          <|> parseNumber
          <|> parseQuoted
          <|> do  char '('
                  x <- (try parseList) <|> parseDottedList 
                  char ')'
                  return x



readExpr :: String -> String
readExpr input = case parse parseExpr "lisp" input of
  Left err    -> "No match: " ++ show err
  Right val   -> "Found Value: " ++ show val


main :: IO ()
main = do 
  args <- getArgs
  putStrLn $ readExpr (args !! 0)
  hFlush stdout
