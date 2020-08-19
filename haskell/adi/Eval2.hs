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
import Error

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Except
import Data.Functor.Identity

type Eval2 = EvalT Identity

instance Eval Eval2 where
    runEval k = snd <$> (runIdentity $ runEvalT k newEnv newHeap)

newtype EvalT m a = EvalT 
    { runEvalT :: Env -> Heap -> m (Either Error (Heap, (a, Log))) }

instance (Monad m) => Functor (EvalT m) where
    fmap f k = EvalT $ \env heap -> do
        (s,(a,w)) <- runEvalT k env heap
        return (s,(f a,w)) 

instance (Monad m) => Applicative (EvalT m) where
    pure  = return
    (<*>) f k = (>>=) f (<$> k)

instance (Monad m) => Monad (EvalT m) where
    return a = EvalT $ \_env heap -> return (heap, (a, mempty))
    k >>= f = EvalT $ \env heap -> do
        (s,(a,w))   <- runEvalT k env heap 
        (s',(b,w')) <- runEvalT (f a) env s
        return (s',(b,w <> w'))

instance (Monad m) => MonadReader Env (EvalT m) where
    ask   = EvalT $ \env heap -> return (heap, (env, mempty))
    local f k = EvalT $ \env heap -> runEvalT k (f env) heap 

instance (Monad m) => MonadWriter Log (EvalT m) where
    tell w = EvalT $ \_env heap -> return (heap, ((),w))
    listen k = EvalT $ \env heap -> do
        (s,(a,w)) <- runEvalT k env heap
        return (s,((a,w),mempty))
    pass k = EvalT $ \env heap -> do
        (s,((a,f),w)) <- runEvalT k env heap
        return (s, (a, f w))

instance (Monad m) => MonadState Heap (EvalT m) where
    get = EvalT $ \_env heap -> return (heap, (heap,mempty))
    put s = EvalT $ \_env _heap -> return (s,((),mempty))

instance (Monad m) => MonadError Error (EvalT m) where
    throwError = undefined
    catchError = undefined
