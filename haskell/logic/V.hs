module V
  ( V(..), W(..)
  , x, y, z, t
  , x', y', z', t'
  ) where

newtype V = V Int deriving (Eq, Ord)
newtype W = W Int deriving (Eq, Ord)

instance Show V where
  show (V 0) = "x"
  show (V 1) = "y"
  show (V 2) = "z"
  show (V 3) = "t"

instance Show W where
  show (W 0) = "x'"
  show (W 1) = "y'"
  show (W 2) = "z'"
  show (W 3) = "t'"

x = V 0
y = V 1 
z = V 2
t = V 3

x' = W 0
y' = W 1 
z' = W 2
t' = W 3



