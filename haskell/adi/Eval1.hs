{-# LANGUAGE GeneralizedNewtypeDeriving     #-}

module  Eval1
    (   eval1
    ,   runEval1
    )   where

import Env
import Log
import Heap
import Value
import Syntax
import Interpret

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Functor.Identity

eval1 :: Expr -> Value
eval1 e = fst $ runEval1 $ eval e

type Eval1 = EvalT Identity

runEval1 :: Eval1 a -> (a, Log)
runEval1 = runIdentity . runEvalT newEnv newHeap

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


