module JNumber
  ( number      -- :: Parser Char Double 
  ) where

import Parser

import Data.Char
import Control.Monad

digit :: Parser Char String       
digit = predicate isDigit 

digits = (greed . plus') digit

-- TODO: replace by library function 
stringToInteger :: String -> Integer
stringToInteger cs = go cs 0 False where
  go []     acc False = acc
  go []     acc True  = -acc
  go (c:cs) acc sign = 
    if isDigit c
      then go cs (10*acc + (toInteger $ digitToInt c)) sign
      else go cs acc (not sign)

natural  :: Parser Char Integer
natural = do
  s <- digits
  return $ stringToInteger s

integer :: Parser Char Integer
integer = do
  s <- option (char '-') <&&> digits
  return $ stringToInteger s

posDouble :: Parser Char Double
posDouble = do
  n1 <- natural 
  s1 <- char '.'
  s2 <- digits
  let n = length s2
  let d1 = fromIntegral n1
  let d2 = fromIntegral (stringToInteger s2)
  let d3 = d2 / (fromIntegral (10^n))
  return $ d1 + d3

posNumber :: Parser Char Double  
posNumber = greed $ posDouble +++ (liftM fromIntegral natural)

number :: Parser Char Double
number = do
  s1 <- option (char '-')
  d1 <- posNumber
  if s1 == "-" 
    then return (-d1) 
    else return d1
 
