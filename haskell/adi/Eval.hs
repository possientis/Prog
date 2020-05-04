{-# LANGUAGE LambdaCase #-}

module  Eval
    (   eval
    )   where

import Data.Functor.Foldable

import Op
import Env
import Var
import Syntax

eval :: Env -> Expr -> Integer
eval env = cata $ \case 
    EVar v     -> evalVar env v
    ENum n     -> evalNum n
    EOp op n m -> evalOp op n m
    EIf z n m  -> evalIf z n m
    _          -> error "eval: evaluation not yet implemented"

evalVar :: Env -> Var -> Integer
evalVar = find

evalNum :: Integer -> Integer 
evalNum = id

evalOp :: Op -> Integer -> Integer -> Integer
evalOp = delta

evalIf :: Integer -> Integer -> Integer -> Integer
evalIf z n m = if z == 0 then n else m
