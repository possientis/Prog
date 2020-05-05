{-# LANGUAGE LambdaCase #-}

module  Eval
    (   eval
    )   where

import Data.Functor.Foldable

import Op
import Env
import Var
import Syntax
import Value

eval :: Env -> Expr -> Value
eval env = cata $ \case 
    EVar x          -> evalVar env x
    ENum n          -> evalNum n
    EOp op v1 v2    -> evalOp op v1 v2
    EIf v v1 v2     -> evalIf v v1 v2
    EApp v1 v2      -> evalApp v1 v2  
    _               -> error "eval: evaluation not yet implemented"

evalVar :: Env -> Var -> Value
evalVar env x = mkVal $ find env x

evalNum :: Integer -> Value
evalNum = mkVal

evalOp :: Op -> Value -> Value -> Value
evalOp op v1 v2 = case val v1 of
    Nothing -> error $ show op ++ ": illegal lhs arg."
    Just n1 -> case val v2 of
        Nothing -> error $ show op ++ ": illegal rhs arg."
        Just n2 -> mkVal $ delta op n1 n2
    
evalIf :: Value -> Value -> Value -> Value
evalIf v v1 v2 = case val v of 
    Nothing -> error "If: cannot evaluate condition."
    Just n  -> if n == 0 then v1 else v2

evalApp :: Value -> Value -> Value
evalApp v1 _v2 = case fun v1 of
    Nothing -> error "App: lhs argument is not a function."
    Just (_x,_e,_env)  -> undefined


