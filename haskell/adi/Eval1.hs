{-# LANGUAGE GeneralizedNewtypeDeriving     #-}

module  Eval1
    (   Eval1
    ,   runEval
    )   where

import Env
import Log
import Heap

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Functor.Identity

type Eval1 = EvalT Identity

runEval :: Eval1 a -> (a, Log)
runEval = runIdentity . runEvalT newEnv newHeap

newtype EvalT m a = EvalT 
    { unEvalT :: ReaderT Env (WriterT Log (StateT Heap m)) a 
    } deriving 
        ( Functor
        , Applicative
        , Monad
        , MonadReader Env
        , MonadWriter Log
        , MonadState Heap
        )

runEvalT 
    :: (Monad m) 
    => Env
    -> Heap 
    -> EvalT m a 
    -> m (a, Log)
runEvalT env heap m  = do
    let m1 = unEvalT m          -- ReaderT Env (WriterT [String] (StateT Heap m)) a
    let m2 = runReaderT m1 env  -- WriterT [String] (StateT Heap m) a
    let m3 = runWriterT m2      -- StateT Heap m (a , [String])
    let m4 = evalStateT m3 heap -- m (a , [String])
    m4


