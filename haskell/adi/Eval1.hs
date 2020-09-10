{-# LANGUAGE FlexibleInstances              #-}
{-# LANGUAGE TypeSynonymInstances           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving     #-}

module  Eval1
    (   Eval1
    )   where

import Env
import Log
import Heap
import Eval
import Error

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Except
import Data.Functor.Identity

type Eval1 = EvalT Identity

instance Eval Eval1 where
    runEval = runIdentity . runEvalT newEnv newHeap

newtype EvalT m a = EvalT 
    { unEvalT :: ReaderT Env (WriterT Log (StateT Heap (ExceptT Error m))) a 
    } deriving 
        ( Functor
        , Applicative
        , Monad
        , MonadReader Env
        , MonadWriter Log
        , MonadState Heap
        , MonadError Error
        )

runEvalT 
    :: (Monad m) 
    => Env
    -> Heap 
    -> EvalT m a 
    -> m (Either Error (a, Log))
runEvalT env heap m  = do
    -- m1 :: ReaderT Env (WriterT Log (StateT Heap (ExceptT Error m)) a
    let m1 = unEvalT m          
    -- m2 :: WriterT Log (StateT Heap (ExceptT Error m)) a
    let m2 = runReaderT m1 env  
    -- m3 :: StateT Heap (ExceptT Error m) (a , Log)
    let m3 = runWriterT m2      
    -- m4 :: (ExcepT Error m) (a , Log)
    let m4 = evalStateT m3 heap 
    -- m5 :: m (Either Error (a, Log))
    let m5 = runExceptT m4
    m5
