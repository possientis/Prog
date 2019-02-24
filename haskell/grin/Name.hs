module  Name
    (   Name (..)
    )   where

import Data.Text

data Name 
    = NM { unNM :: !Text }
    | NI !Int
    deriving (Eq, Ord, Show)
