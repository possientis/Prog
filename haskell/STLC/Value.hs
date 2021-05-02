module  Value
    (   Value   (..)
    ,   Neutral (..)
    ,   vfree
    )   where

import Syntax

data Value 
    = VLam (Value -> Value)
    | VNeutral Neutral

data Neutral
    = NFree Name
    | NApp Neutral Value

vfree :: Name -> Value
vfree n = VNeutral (NFree n)





