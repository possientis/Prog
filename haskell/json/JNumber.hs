module JNumber
  ( number      -- :: Parser Char Double 
  ) where

import Parser

import Data.Char
import Control.Monad
import Control.Applicative ((<$>))

digit :: Parser Char String       
digit = sat isDigit 

digits = (greed . plus') digit

number :: Parser Char Double
number = do
  s <- option(char '-') <&&> digits <&&> option (char '.' <&&> digits)
  return $ read s

