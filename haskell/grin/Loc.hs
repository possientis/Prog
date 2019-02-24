module  Loc
    (   Loc (..)
    )   where

newtype Loc = Loc { unLoc :: Int } deriving (Eq, Ord, Show)
