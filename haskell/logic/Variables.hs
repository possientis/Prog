module Variables 
  ( V(..)
  , x
  , y
  , z
  ) where

newtype V = V Int deriving (Eq)

instance Show V where
  show (V 0) = "x"
  show (V 1) = "y"
  show (V 2) = "z"

x = V 0
y = V 1 
z = V 2


