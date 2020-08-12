{-# LANGUAGE FlexibleInstances              #-}
{-# LANGUAGE TypeSynonymInstances           #-}
{-# LANGUAGE MultiParamTypeClasses          #-}

module  Eval2
    (   Eval2
    )   where

import Env
import Log
import Heap
import Eval

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Functor.Identity

type Eval2 = EvalT Identity

instance Eval Eval2 where
    runEval k = snd . runIdentity $ runEvalT k newEnv newHeap

newtype EvalT m a = EvalT { runEvalT :: Env -> Heap -> m (Heap, (a, Log)) }

instance (Monad m) => Functor (EvalT m) where
    fmap f k = EvalT $ \env heap -> do
        (s,(a,w)) <- runEvalT k env heap
        return (s,(f a,w)) 

instance (Monad m) => Applicative (EvalT m) where

instance (Monad m) => Monad (EvalT m) where

instance (Monad m) => MonadReader Env (EvalT m) where

instance (Monad m) => MonadWriter Log (EvalT m) where

instance (Monad m) => MonadState Heap (EvalT m) where
