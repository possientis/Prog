{-# LANGUAGE LambdaCase #-}

module  Interpret
    (   eval
    ,   evalIO
    )   where

import Data.Functor.Foldable

import Op
import Env
import Var
import Eval
import Value
import Syntax
import Closure

evalIO :: Expr -> IO ()
evalIO e = do
    let (res,logs) = runEval $ eval' e
    mapM_ putStrLn logs
    print res
    
eval :: Expr -> Value
eval e = fst $ runEval $ eval' e

eval' :: Expr -> Eval Value
eval' e = eval_ e eval'

eval_ :: Expr -> (Expr -> Eval Value) -> Eval Value
eval_ = \case 
    Fix (ENum n)        -> evalNum n
    Fix (EVar x)        -> evalVar x
    Fix (EOp op e1 e2)  -> evalOp op e1 e2
    Fix (EIf e e1 e2)   -> evalIf e e1 e2
    Fix (ELam x e)      -> evalLam x e
    Fix (EApp e1 e2)    -> evalApp e1 e2  
    Fix (ERec f e)      -> evalRec f e

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
            v2   <- ev e2 
            addr <- alloc
            write addr v2
            let env = closureEnv c
            let x   = closureVar c
            let e   = closureBody c
            v <- localEnv (bind x addr env) (ev e)
            return v

evalRec :: Var -> Expr -> (Expr -> Eval Value) -> Eval Value
evalRec f e ev = do
    env  <- askEnv
    addr <- alloc 
    let env' = bind f addr env
    v <- localEnv env' (ev e)
    write addr v
    return v
