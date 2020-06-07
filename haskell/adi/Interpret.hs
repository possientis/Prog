{-# LANGUAGE LambdaCase #-}

module  Interpret
    (   eval
    )   where

import Data.Functor.Foldable

--import Op
import Var
import Eval
import Value
import Syntax

eval :: Expr -> (Expr -> Eval Value) -> Eval Value
eval = \case 
    Fix (ENum n)        -> evalNum n
    Fix (EVar x)        -> evalVar x
    _                   -> error "not implemented"
{-
    Fix (EOp op e1 e2)  -> evalOp op e1 e2
    Fix (EIf e e1 e2)   -> evalIf e e1 e2
    Fix (ELam x e)      -> evalLam x e
    Fix (EApp v1 v2)    -> evalApp v1 v2  
    Fix (ERec f e)      -> evalRec f e
-}


evalNum :: Integer -> (Expr -> Eval Value) -> Eval Value
evalNum n _eval = return $ mkVal n

evalVar :: Var -> (Expr -> Eval Value) -> Eval Value
evalVar _x _eval = undefined

{-
evalOp :: Op -> Expr -> Expr -> Env -> Value
evalOp op e1 e2 env = case val (eval e1 env) of
    Nothing -> error $ show op ++ ": lhs does not evaluate to an integer."
    Just n1 -> case val (eval e2 env) of
        Nothing -> error $ show op ++ ": rhs does not evaluate to an integer."
        Just n2 -> mkVal $ delta op n1 n2
   
evalIf :: Expr -> Expr -> Expr -> Env -> Value
evalIf e e1 e2 env = case val (eval e env) of 
    Nothing -> error "If: condition does not evaluate to an integer."
    Just n  -> if n == 0 then (eval e1 env) else (eval e2 env)

evalLam :: Var -> Expr -> Env -> Value
evalLam x e env = mkClosure x e env 

evalApp :: Expr -> Expr -> Env -> Value
evalApp e1 e2 env = case closure (eval e1 env) of
    Nothing -> error "App: lhs does not evaluate to a function."
    Just c  -> evalClosure c (eval e2 env) 

evalRec :: Var -> Expr -> Env -> Value
evalRec f e env = eval e (bind f (mkExpr e) env)

-- Given a value to which the closure variable is bound, 
-- returns the value corresponding to the closure evaluation.
-- This is simply the value obtained by evaluating the closure 
-- body in the 'local environment', defined as the closure 
-- environment with the additional binding of the closure 
-- variable to the value argument.
evalClosure :: Closure -> Value -> Value
evalClosure c v = eval (closureBody c) (bind (closureVar c) v (closureEnv c))
-}
