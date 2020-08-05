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

--import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Functor.Identity

type Eval = EvalT Identity

runEval :: Eval a -> (a, [String])
runEval = runIdentity . runEvalT newEnv newHeap


newtype EvalT m a = EvalT 
    { unEvalT :: ReaderT Env (WriterT [String] (StateT Heap m)) a 
    } deriving 
        ( Functor
        , Applicative
        , Monad
        , MonadReader Env
        , MonadWriter [String]
        , MonadState Heap
        )

runEvalT 
    :: (Monad m) 
    => Env
    -> Heap 
    -> EvalT m a 
    -> m (a, [String])
runEvalT env heap m  = do
    let m1 = unEvalT m          -- ReaderT Env (WriterT [String] (StateT Heap m)) a
    let m2 = runReaderT m1 env  -- WriterT [String] (StateT Heap m) a
    let m3 = runWriterT m2      -- StateT Heap m (a , [String])
    let m4 = evalStateT m3 heap -- m (a , [String])
    m4

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
    tell ["write at address " ++ show addr ++ ": " ++ show v]

write :: Addr -> Value -> Eval ()
write = writeT

-- run computation in a local environment
localEnvT :: (Monad m) => Env -> EvalT m Value -> EvalT m Value
localEnvT env ev = EvalT $ ReaderT $ const $ runReaderT (unEvalT ev) env

localEnv :: Env -> Eval Value -> Eval Value
localEnv = localEnvT
