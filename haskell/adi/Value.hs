{-# LANGUAGE LambdaCase     #-}

module  Value
    (   Value
    ,   mkNil
    ,   mkNum
    ,   mkBool
    ,   mkClo
    ,   num
    ,   bool
    ,   closure
    )   where

import Var
import Env
import Syntax
import Closure

data Value 
    = Nil 
    | Num  Integer
    | Bool Bool
    | Clo  Closure

instance Show Value where
    show = \case 
        Nil     -> "<nil>"
        Num  n  -> show n
        Bool b  -> show b
        Clo  c  -> show c

mkNil :: Value 
mkNil = Nil

mkNum :: Integer -> Value
mkNum = Num

mkBool :: Bool -> Value
mkBool = Bool

mkClo :: Var -> Expr -> Env -> Value
mkClo x e env = Clo $ mkClosure x e env

num :: Value -> Maybe Integer
num = \case
    Num n   -> Just n
    _       -> Nothing

bool :: Value -> Maybe Bool
bool = \case
    Bool b  -> Just b
    _       -> Nothing

closure :: Value -> Maybe Closure
closure = \case
    Clo c   -> Just c
    _       -> Nothing
