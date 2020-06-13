{-# LANGUAGE LambdaCase #-}

module  Interpret
    (   eval
    )   where

import Data.Functor.Foldable

import Op
import Env
import Var
import Eval
import Value
import Syntax

eval :: Expr -> (Expr -> Eval Value) -> Eval Value
eval = \case 
    Fix (ENum n)        -> evalNum n
    Fix (EVar x)        -> evalVar x
    Fix (EOp op e1 e2)  -> evalOp op e1 e2
    Fix (EIf e e1 e2)   -> evalIf e e1 e2
    Fix (ELam x e)      -> evalLam x e
    Fix (EApp e1 e2)    -> evalApp e1 e2  
    _                   -> error "not implemented"
{-
    Fix (ERec f e)      -> evalRec f e
-}

evalNum :: Integer -> (Expr -> Eval Value) -> Eval Value
evalNum n _ev = return $ mkVal n

evalVar :: Var -> (Expr -> Eval Value) -> Eval Value
evalVar x _ev = do
    env <- askEnv
    find (findAddr env x)

evalOp :: Op -> Expr -> Expr -> (Expr -> Eval Value) -> Eval Value
evalOp op e1 e2 ev =  do
    v1 <- ev e1
    v2 <- ev e2
    case val v1 of
        Nothing -> error $ show op ++ ": lhs does not evaluate to an integer."
        Just n1 -> case val v2 of
            Nothing -> error $ show op ++ ": rhs does not evaluate to an integer."
            Just n2 -> return $ mkVal $ delta op n1 n2

evalIf :: Expr -> Expr -> Expr -> (Expr -> Eval Value) -> Eval Value
evalIf e e1 e2 ev = do
    v <- ev e
    case val v of
        Nothing -> error "If: condition does not evaluate to an integer."
        Just n  -> ev $ if n == 0 then e1 else e2

evalLam :: Var -> Expr -> (Expr -> Eval Value) -> Eval Value
evalLam x e _ev = do
    env <- askEnv
    return $ mkClo x e env 

evalApp :: Expr -> Expr -> (Expr -> Eval Value) -> Eval Value
evalApp e1 e2 ev = do
    v1 <- ev e1
    case closure v1 of
        Nothing -> error "App: lhs does not evaluate to a function."
        Just c  -> do 
            v1   <- ev e1 
            addr <- alloc
            return undefined

{-

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
