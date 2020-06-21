{-# LANGUAGE GeneralizedNewtypeDeriving     #-}

module  Eval
    (   Eval
    ,   runEval
    ,   askEnv
    ,   find
    ,   alloc
    ,   write
    ,   localEnv
    )   where

import Env
import Addr
import Heap
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

allocT :: (Monad m) => EvalT m Addr
allocT = do
    (heap,addr) <- heapAlloc <$> get
    put heap
    return addr

alloc :: Eval Addr
alloc = allocT

writeT :: (Monad m) => Addr -> Value -> EvalT m ()
writeT addr v = do
    heap <- heapWrite addr v <$> get
    put heap

write :: Addr -> Value -> Eval ()
write = writeT

-- run computation in a local environment
localEnvT :: (Monad m) => Env -> EvalT m Value -> EvalT m Value
localEnvT env ev = EvalT $ ReaderT $ const $ runReaderT (unEvalT ev) env

localEnv :: Env -> Eval Value -> Eval Value
localEnv = localEnvT
