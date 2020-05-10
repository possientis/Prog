{-# LANGUAGE LambdaCase #-}

module  Eval
    (   eval
    )   where

import Data.Functor.Foldable

import Op
import Env
import Var
import Syntax

eval :: Expr -> Env -> Value
eval = cata $ \case 
    EVar x          -> evalVar x
    ENum n          -> evalNum n
    EOp op v1 v2    -> evalOp op v1 v2
    EIf v v1 v2     -> evalIf v v1 v2
    EApp v1 v2      -> evalApp v1 v2  
    ELam x v        -> evalLam x v
--    _               -> error "eval: evaluation not yet implemented"

evalVar :: Var -> Env -> Value
evalVar = find

evalNum :: Integer -> Env -> Value
evalNum n _ = mkVal n

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
    
evalIf 
    :: (Env -> Value) 
    -> (Env -> Value) 
    -> (Env -> Value) 
    -> Env 
    -> Value
evalIf v v1 v2 env = case val (v env) of 
    Nothing -> error "If: cannot evaluate condition."
    Just n  -> if n == 0 then (v1 env) else (v2 env)

evalApp 
    :: (Env -> Value) 
    -> (Env -> Value) 
    -> Env 
    -> Value
evalApp v1 v2 env = case fun (v1 env) of
    Nothing -> error "App: lhs argument is not a function."
    Just (x, v, envLocal)  -> v env' where 
        env' = bind x (v2 env) envLocal  

evalLam :: Var -> (Env -> Value) -> Env -> Value
evalLam x v env = mkFun x v env 

