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
        res <- runEvalT k env heap
        return $ case res of
            Left err        -> Left err
            Right (s,(a,w)) -> Right (s,(f a,w)) 

instance (Monad m) => Applicative (EvalT m) where
    pure  = return
    (<*>) f k = (>>=) f (<$> k)

instance (Monad m) => Monad (EvalT m) where
    return a = EvalT $ \_env heap -> return . Right $ (heap, (a, mempty))
    k >>= f = EvalT $ \env heap -> do
        res <- runEvalT k env heap 
        case res of 
            Left err        -> return . Left $ err
            Right (s,(a,w)) -> do
                res' <- runEvalT (f a) env s
                return $ case res' of
                    Left err            -> Left err
                    Right (s',(b,w'))   -> Right (s',(b,w <> w'))

instance (Monad m) => MonadReader Env (EvalT m) where
    ask   = EvalT $ \env heap -> return . Right $ (heap, (env, mempty))
    local f k = EvalT $ \env heap -> runEvalT k (f env) heap 

instance (Monad m) => MonadWriter Log (EvalT m) where
    tell w = EvalT $ \_env heap -> return . Right $ (heap, ((),w))
    listen k = EvalT $ \env heap -> do
        res <- runEvalT k env heap
        return $ case res of
            Left err        -> Left err
            Right (s,(a,w)) -> Right (s,((a,w),mempty))
    pass k = EvalT $ \env heap -> do
        res <- runEvalT k env heap
        return $ case res of
            Left err            -> Left err
            Right (s,((a,f),w)) -> Right (s, (a, f w))

instance (Monad m) => MonadState Heap (EvalT m) where
    get = EvalT $ \_env heap -> return . Right $ (heap, (heap,mempty))
    put s = EvalT $ \_env _heap -> return . Right $ (s,((),mempty))

instance (Monad m) => MonadError Error (EvalT m) where
    throwError = undefined
    catchError = undefined
