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
    Fix (ENum n)            -> evalNum n
    Fix (EBool b)           -> evalBool b
    Fix (EVar x)            -> evalVar x
    Fix (EOp op es)         -> evalOp op es
    Fix (EIf e e1 e2)       -> evalIf e e1 e2
    Fix (ELam x e)          -> evalLam x e
    Fix (EApp e1 e2)        -> evalApp e1 e2  
    Fix (ERec f e)          -> evalRec f e
    Fix (EZero)             -> evalZero
    Fix (ESuc e)            -> evalSuc e
    Fix (ECase e e1 x e2)   -> evalCase e e1 x e2  

evalNum :: Integer -> (Expr -> Eval Value) -> Eval Value
evalNum n _ev = return $ mkNum n

evalBool :: Bool -> (Expr -> Eval Value) -> Eval Value
evalBool b _ev = return $ mkBool b

evalVar :: Var -> (Expr -> Eval Value) -> Eval Value
evalVar x _ev = do
    env <- askEnv
    find (findAddr env x)

evalOp :: Op -> [Expr] -> (Expr -> Eval Value) -> Eval Value
evalOp op es ev = delta op <$> mapM ev es

evalIf :: Expr -> Expr -> Expr -> (Expr -> Eval Value) -> Eval Value
evalIf e e1 e2 ev = do
    v <- ev e
    case num v of
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

evalZero :: (Expr -> Eval Value) -> Eval Value
evalZero _ev = return mkZero

evalSuc :: Expr -> (Expr -> Eval Value) -> Eval Value
evalSuc e ev = do
    v <- ev e
    case nat v of 
        Nothing -> error "Suc: argument is not a Nat."
        Just v' -> return $ mkSuc $ v'

evalCase :: Expr -> Expr -> Var -> Expr -> (Expr -> Eval Value) -> Eval Value
evalCase e e1 _x _e2 ev = do
    v <- ev e
    if isZero v then ev e1 else
        case suc v of
            Nothing -> error "Case: expression does not evaluate to a Nat."
            Just _v  -> do 
                undefined
