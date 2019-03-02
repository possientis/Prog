module  Domain
    (   
    )   where

import Data.Text
import Data.Word
import Data.Int

newtype Loc = Loc { unLoc :: Int } deriving (Eq, Ord, Show)

newtype DName = DName { unDName :: Text } deriving (Eq, Ord, Show) 


data DVal 
    = DInt64  Int64
    | DWord64 Word64
    | DFloat  Float
    | DBool   Bool
    | DString String
    | DChar   Char
    | DLoc    Loc
    | DUnit
    | DBot
    | DNode DName [DVal]
    deriving (Eq, Ord, Show) 

