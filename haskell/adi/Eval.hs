{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}


module  Eval
    (   Eval    (..)
    ,   eval
    ,   evalLog
    ,   evalAll
    ,   evalIO
    )   where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Functor.Foldable

import Op
import Env
import Var
import Log
import Heap
import Prim
import Value
import Pretty
import Syntax
import Closure

class 
    ( MonadReader Env m
    , MonadWriter Log m
    , MonadState Heap m 
    ) => Eval m where

    runEval :: m a -> (a,Log)

  
eval :: forall m . (Eval m) => Expr -> Value
eval = fst . (evalAll @ m)

evalLog :: forall m . (Eval m) => Expr -> Log
evalLog = snd . (evalAll @ m)

evalAll :: forall m . (Eval m) => Expr -> (Value, Log)
evalAll e = runEval $ (eval' @ m) e

evalIO :: forall m . (Eval m) => Expr -> IO ()
evalIO e = do
    putStrLn $ "\nExpression: " ++ showExpr e ++ "\n"
    let (v,w) = (evalAll @ m) e
    mapM_ putStrLn w
    putStrLn $ "\nResult: " ++ show v ++ "\n"

eval' :: (Eval m) => Expr -> m Value
eval' e = do
    env <- ask
    tell ["Evaluating exp = " ++ showExpr e ++ ", env = " ++ show env ]
    eval_ e eval'

eval_ :: (Eval m) => Expr -> (Expr -> m Value) -> m Value
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

evalNum 
    :: (Eval m) 
    => Integer 
    -> (Expr -> m Value) 
    -> m Value
evalNum n _ev = return $ mkNum n

evalBool 
    :: (Eval m) 
    => Bool 
    -> (Expr -> m Value) 
    -> m Value
evalBool b _ev = return $ mkBool b

evalVar 
    :: (Eval m) 
    => Var 
    -> (Expr -> m Value)    
    -> m Value
evalVar x _ev = do
    env <- askEnv
    find (findAddr env x)

evalOp 
    :: (Eval m) 
    => Op 
    -> [Expr] 
    -> (Expr -> m Value) 
    -> m Value
evalOp op es ev = delta op <$> mapM ev es

evalIf 
    :: (Eval m) 
    => Expr 
    -> Expr 
    -> Expr 
    -> (Expr -> m Value) 
    -> m Value
evalIf e e1 e2 ev = do
    v <- ev e
    case bool v of
        Nothing -> error "If: condition does not evaluate to a boolean."
        Just b  -> ev $ if b then e1 else e2

evalLam 
    :: (Eval m) 
    => Var 
    -> Expr 
    -> (Expr -> m Value) 
    -> m Value
evalLam x e _ev = do
    env <- askEnv
    return $ mkClo x e env 

evalApp 
    :: (Eval m) 
    => Expr 
    -> Expr 
    -> (Expr -> m Value) 
    -> m Value
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
            localEnv (bind x addr env) (ev e)

evalRec 
    :: (Eval m) 
    => Var 
    -> Expr 
    -> (Expr -> m Value) 
    -> m Value
evalRec f e ev = do
    env  <- askEnv
    addr <- alloc 
    let env' = bind f addr env
    v <- localEnv env' (ev e)
    write addr v
    return v

evalZero 
    :: (Eval m)
    => (Expr -> m Value) 
    -> m Value
evalZero _ev = return mkZero

evalSuc 
    :: (Eval m)
    => Expr 
    -> (Expr -> m Value) 
    -> m Value
evalSuc e ev = do
    v <- ev e
    case nat v of 
        Nothing -> error "Suc: argument is not a Nat."
        Just v' -> return $ mkSuc $ v'

evalCase 
    :: (Eval m) 
    => Expr 
    -> Expr 
    -> Var 
    -> Expr 
    -> (Expr -> m Value) 
    -> m Value
evalCase e e1 x e2 ev = do
    v <- ev e
    if isZero v then ev e1 else
        case suc v of
            Nothing -> error "Case: expression does not evaluate to a Nat."
            Just v'  -> do 
                env <- askEnv
                addr <- alloc
                write addr v'
                localEnv (bind x addr env) (ev e2)
