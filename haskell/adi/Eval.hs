{-# LANGUAGE GeneralizedNewtypeDeriving     #-}

module  Eval
    (   Eval
    ,   runEval
    ,   askEnv
    ,   find
--    ,   alloc
--    ,   write
--    ,   localEnv
--    ,   runEval
    )   where

import Env
import Addr
import Heap
import State
import Value

import Control.Monad.State
import Control.Monad.Reader
import Data.Functor.Identity

type Eval = EvalT Identity

runEval :: Eval a -> a
runEval = runIdentity . runEvalT newEnv newHeap

newtype EvalT m a = EvalT 
    { unEvalT :: ReaderT Env (StateT Heap m) a 
    } deriving 
        ( Functor
        , Applicative
        , Monad
        , MonadReader Env
        , MonadState Heap
        )

runEvalT 
    :: (Monad m) 
    => Env
    -> Heap 
    -> EvalT m a 
    -> m a
runEvalT env heap m  = evalStateT (runReaderT (unEvalT m) env) heap

askEnvT :: (Monad m) => EvalT m Env
askEnvT  = ask

askEnv :: Eval Env
askEnv = askEnvT

findT :: (Monad m) => Addr -> EvalT m Value
findT addr = findVal addr <$> get

find :: Addr -> Eval Value
find = findT

{-

find :: Addr -> Eval Value
find addr = Eval $ do
    heap <- gets getHeap
    return $ findVal heap addr 

alloc :: Eval Addr
alloc = Eval $ do
    s <- get
    let heap = getHeap s
    let (heap',addr) = heapAlloc heap
    let s' = setHeap heap' s
    put s'
    return addr

write :: Addr -> Value -> Eval ()
write addr v = Eval $ do
    s <- get
    let heap = getHeap s
    let heap' = heapWrite heap addr v
    let s' = setHeap heap' s
    put s'
    return () 

-- run computation in a local environment
localEnv :: Env -> Eval Value -> Eval Value
localEnv env ev = Eval $ do
    s0 <- get
    let env0 = getEnv s0
    let s1 = setEnv env s0
    put s1
    v <- unEval ev
    s2 <- get
    let s3 = setEnv env0 s2
    put s3
    return v
-}
