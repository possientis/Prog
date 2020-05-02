module  Var 
    (   Var   
    ,   mkVar
    )   where

newtype Var = Var { _unVar :: String }
    deriving (Eq, Ord)

mkVar :: String -> Var
mkVar = Var
