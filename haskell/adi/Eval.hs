{-# LANGUAGE LambdaCase #-}

module  Eval
    (   eval
    ,   eval'
    )   where

import Data.Functor.Foldable

import Op
import Env
import Var
import Syntax

eval :: Expr -> Env -> Value
eval = cata $ \case 
    ENum n          -> evalNum n
    EVar x          -> evalVar x
    EOp op v1 v2    -> evalOp op v1 v2
    EIf v v1 v2     -> evalIf v v1 v2
    EApp v1 v2      -> evalApp v1 v2  
    ELam x v        -> evalLam x v

eval' :: Expr -> Env' -> Expr
eval' = cata $ \case
    ENum n          -> evalNum' n
    EVar x          -> evalVar' x
    EOp op e1 e2    -> evalOp' op e1 e2
    _               -> error "not implemented"

evalNum :: Integer -> Env -> Value
evalNum n _ = mkVal n

evalNum' :: Integer -> Env' -> Expr
evalNum' n _ = eNum n

evalVar :: Var -> Env -> Value
evalVar = find

evalVar' :: Var -> Env' -> Expr
evalVar' = find'

evalOp 
    :: Op 
    -> (Env -> Value) 
    -> (Env -> Value) 
    -> Env 
    -> Value
evalOp op v1 v2 env = case val (v1 env) of
    Nothing -> error $ show op ++ ": illegal lhs arg."
    Just n1 -> case val (v2 env) of
        Nothing -> error $ show op ++ ": illegal rhs arg."
        Just n2 -> mkVal $ delta op n1 n2
evalOp' 
    :: Op 
    -> (Env' -> Expr) 
    -> (Env' -> Expr) 
    -> Env'
    -> Expr
evalOp' op e1 e2 env = case toNum (e1 env) of
    Nothing -> error $ show op ++ ": illegal lhs arg."
    Just n1 -> case toNum (e2 env) of
        Nothing -> error $ show op ++ ": illegal rhs arg."
        Just n2 -> eNum $ delta op n1 n2
    
evalIf 
    :: (Env -> Value) 
    -> (Env -> Value) 
    -> (Env -> Value) 
    -> Env 
    -> Value
evalIf v v1 v2 env = case val (v env) of 
    Nothing -> error "If: cannot evaluate condition."
    Just n  -> if n == 0 then (v1 env) else (v2 env)

evalLam :: Var -> (Env -> Value) -> Env -> Value
evalLam x v env = mkClosure x v env 

evalApp 
    :: (Env -> Value) 
    -> (Env -> Value) 
    -> Env 
    -> Value
evalApp v1 v2 env = case closure (v1 env) of
    Nothing -> error "App: lhs argument is not a function."
    Just c  -> evalClosure c (v2 env) 


