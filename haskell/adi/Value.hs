{-# LANGUAGE LambdaCase     #-}

module  Value
    (   Value
    ,   mkVal
    ,   mkFun
    ,   val
    ,   fun
    )   where

import Var
import Env
import Syntax

data Value 
    = Val Integer
    | Fun Var Expr Env 

mkVal :: Integer -> Value
mkVal = Val

mkFun :: Var -> Expr -> Env -> Value
mkFun = Fun

val :: Value -> Maybe Integer
val = \case
    Val n       -> Just n
    Fun _ _ _   -> Nothing

fun :: Value -> Maybe (Var, Expr, Env)
fun = \case
    Val _       -> Nothing
    Fun x e env -> Just (x, e, env)
