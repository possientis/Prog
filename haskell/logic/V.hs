module V
  ( V(..), W(..)
  , x, y, z
  , x', y', z'
  ) where

newtype V = V Int deriving (Eq, Ord)
newtype W = W Int deriving (Eq, Ord)

instance Show V where
  show (V 0) = "x"
  show (V 1) = "y"
  show (V 2) = "z"

instance Show W where
  show (W 0) = "x'"
  show (W 1) = "y'"
  show (W 2) = "z'"

x = V 0
y = V 1 
z = V 2

x' = W 0
y' = W 1 
z' = W 2



