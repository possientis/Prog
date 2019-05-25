module  Haskell.TypeCheck
    (   Exp     (..)
    ,   Type    (..)
    ,   hasType
    )   where

data Exp
    = LNat  Integer
    | LBool Bool
    | Plus  Exp Exp
    | And   Exp Exp 

data Type = TNat | TBool


hasType :: Exp -> Type -> Bool
hasType (LNat _)        TNat                                        = True
hasType (LNat _)        _                                           = False
hasType (LBool _)       TBool                                       = True
hasType (LBool _)       _                                           = False
hasType (Plus e1 e2)    TNat | hasType e1 TNat , hasType e2 TNat    = True
hasType (Plus _ _)      _                                           = False
hasType (And e1 e2)     TBool | hasType e1 TBool, hasType e2 TBool  = True
hasType (And _  _)      _                                           = False


typeCheck :: Exp -> Maybe Type
typeCheck = undefined
