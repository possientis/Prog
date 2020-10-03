module  EType 
    (   EType   (..)
    )   where

infixr 9 :->

data EType = TNat | TNum | TBool | EType :-> EType
