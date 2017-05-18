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

parseString :: Stream s m Char => ParsecT s u m LispVal
parseString = do 
  char '"'
  x <- many (noneOf "\"")
  char '"'
  return $ String x


readExpr :: Stream s Identity Char => s -> String
readExpr input = case parse (spaces >> symbol) "lisp" input of 
  Left err  -> "No match: " ++ show err
  Right val -> "Found value"


main :: IO ()
main = do 
  args <- getArgs
  putStrLn $ readExpr (args !! 0)
  hFlush stdout
