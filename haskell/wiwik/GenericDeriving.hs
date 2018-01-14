{-# LANGUAGE DeriveGeneric #-}


import Data.Hashable
import GHC.Generics (Generic)

data Color = Red | Green | Blue deriving (Generic, Show)

instance Hashable Color where

ex1 :: Int
ex1 = hash Red

ex2 :: Int
ex2 = hashWithSalt 0xDEADBEEF Red
