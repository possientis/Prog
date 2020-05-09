{-# LANGUAGE LambdaCase     #-}

module  Env
    (   Env
    ,   Value
    ,   newEnv
    ,   find
    ,   mkVal
    ,   mkFun
    ,   val
    ,   fun
    ,   bind
    )   where

import Data.Map.Strict as M

import Var
import Syntax

newtype Env = Env { unEnv :: Map Var Value }

data Value 
    = Val Integer
    | Fun Var Expr Env 

newEnv :: Env
newEnv = Env mempty

find :: Var -> Env -> Value
find var env = case M.lookup var (unEnv env) of
    Just v  -> v
    Nothing -> error $ "Variable unbound:" ++ show var

-- Add binding to existing environment
bind :: Var -> Value -> Env -> Env
bind x v env = Env $ insert x v (unEnv env)

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
