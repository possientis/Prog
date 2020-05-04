module  Var 
    (   Var   
    ,   mkVar
    )   where

newtype Var = Var { unVar :: String }
    deriving (Eq, Ord)

instance Show Var where
    show = unVar

mkVar :: String -> Var
mkVar = Var
