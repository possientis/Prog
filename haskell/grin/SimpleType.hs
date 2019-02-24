{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE TypeFamilies   #-}
{-# LANGUAGE TypeOperators  #-}

module  SimpleType
    (   SimpleType (..)
    ,   Denote
    )   where 

import Data.Int     (Int64)
import Data.Word    (Word64)
import Data.Text    (Text)

import Loc

data SimpleType
    = T_Int64
    | T_Word64
    | T_Float
    | T_Bool
    | T_Unit
    | T_Location {_locations :: [Loc]}
    | T_UnspecifiedLocation
    | T_Dead
    | T_String
    | T_Char
    deriving (Eq, Ord, Show)


type family Denote a where
    Denote 'T_Int64               = Int64
    Denote 'T_Word64              = Word64
    Denote 'T_Float               = Float
    Denote 'T_Bool                = Bool
    Denote 'T_Unit                = ()
    Denote ('T_Location ls)       = ()    -- TBA
    Denote 'T_UnspecifiedLocation = ()    -- TBA
    Denote 'T_Dead                = ()    -- TBA
    Denote 'T_String              = Text
    Denote 'T_Char                = Char




    
