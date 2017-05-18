{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Control.Monad.State hiding (runStateT, StateT, runState, State)

newtype State s a = State { runState :: s -> (a,s) }

instance Applicative (State s) where
  pure  = return
  (<*>) = ap

instance Functor (State s) where
  fmap  = liftM

instance Monad (State s) where
  return a  = State $ \s -> (a,s)
  (>>=) k f = State $ \s -> let (a,s') = runState k s in runState (f a) s'


newtype StateT s m a  = StateT { runStateT :: s -> m (a,s) }

instance Monad m => Applicative (StateT s m) where
  pure  = return
  (<*>) = ap

instance Monad m => Functor (StateT s m) where
  fmap = liftM

instance Monad m => Monad (StateT s m) where
  return  a = StateT $ \s -> return (a,s)
  (>>=) k f = StateT $ \s -> do
    (a, s') <- runStateT k s
    runStateT (f a) s'

instance MonadTrans (StateT s) where
  lift k  = StateT $ \s -> do { a <- k; return (a,s) }


instance Monad m => MonadState s (StateT s m) where
  get   = StateT $ \s -> return (s,s)
  put s = StateT $ \_ -> return ((),s)

instance MonadPlus m => Alternative (StateT s m) where
  empty = mzero
  (<|>) = mplus

instance MonadPlus m => MonadPlus (StateT s m) where
  mzero = StateT $ \s -> mzero
  mplus (StateT x) (StateT y) = StateT $ \s -> mplus (x s) (y s)
