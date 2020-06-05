{-# LANGUAGE LambdaCase     #-}

module  Value
    (   Value
    ,   mkNil
    ,   mkVal
    ,   mkClo
    ,   val
    ,   closure
    )   where

import Var
import Env
import Syntax
import Closure

data Value 
    = Nil 
    | Val Integer
    | Clo Closure

instance Show Value where
    show = \case 
        Nil     -> "<nil>"
        Val n   -> show n
        Clo c   -> show c

mkNil :: Value 
mkNil = Nil

mkVal :: Integer -> Value
mkVal = Val

mkClo :: Var -> Expr -> Env -> Value
mkClo x e env = Clo $ mkClosure x e env

val :: Value -> Maybe Integer
val = \case
    Val n   -> Just n
    _       -> Nothing

closure :: Value -> Maybe Closure
closure = \case
    Clo c   -> Just c
    _       -> Nothing
