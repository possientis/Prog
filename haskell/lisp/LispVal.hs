module LispVal
  ( LispVal(..)
  ) where

data LispVal  = Atom String
              | List [LispVal] 
              | DottedList [LispVal] LispVal
              | Number Integer
              | String String
              | Bool Bool
              | Char Char
              deriving (Show, Eq)



