{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module  RWS
    (   RWST        (..)
    ,   evalRWST
    ,   execRWST
    ,   mapRWST
    ,   withRWST
    ,   fromRWST
    ,   toRWST
    )   where

import Control.Monad       
import Control.Monad.Fix
import Control.Monad.Fail           as Fail
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State

import Control.Applicative 

import Data.Functor.Contravariant


newtype RWST r w s m a = RWST { runRWST :: r -> s -> m (a,s,w) }

evalRWST :: (Monad m) => RWST r w s m a -> r -> s -> m (a,w)
evalRWST m r s = do
    (a,_,w) <- runRWST m r s
    return (a,w)

execRWST :: (Monad m) => RWST r w s m a -> r -> s -> m (s,w)
execRWST m r s = do
    (_,s',w) <- runRWST m r s
    return (s',w)

mapRWST :: (m (a,s,w) -> n (b,s,w')) -> RWST r w s m a -> RWST r w' s n b
mapRWST f m = RWST $ \r s -> f(runRWST m r s)

withRWST :: (r' -> s -> (r,s)) -> RWST r w s m a -> RWST r' w s m a
withRWST f m = RWST $ \r' s -> uncurry (runRWST m) $ f r' s   

instance (Functor m) => Functor (RWST r w s m) where
    fmap f m = RWST $ \r s -> fmap (\(a,s',w) -> (f a,s',w)) $ runRWST m r s

instance (Monoid w, Monad m) => Applicative (RWST r w s m) where
    pure a = RWST $ \_ s -> return $ (a, s, mempty)
    mf <*> ma = RWST $ \r s -> do
        (f,s',w)   <- runRWST mf r s 
        (a,s'',w') <- runRWST ma r s'
        return (f a, s'', w `mappend` w')

instance (Monoid w, MonadPlus m) => Alternative (RWST r w s m) where
    empty = RWST $ \_ _ -> mzero 
    m <|> m' = RWST $ \r s -> runRWST m r s `mplus` runRWST m' r s

instance (Monoid w, Monad m) => Monad (RWST r w s m) where
    m >>= f = RWST $ \r s -> do
        (a,s',w)   <- runRWST m r s 
        (b,s'',w') <- runRWST (f a) r s'
        return (b,s'',w `mappend` w')

instance (Monoid w, MonadFail m) => MonadFail (RWST r w s m) where
    fail msg = RWST $ \_ _ -> Fail.fail msg

instance (Monoid w, MonadPlus m) => MonadPlus (RWST r w s m) where
    mzero = RWST $ \_ _ -> mzero 
    m `mplus` m' = RWST $ \r s -> runRWST m r s `mplus` runRWST m' r s

instance (Monoid w, MonadFix m) => MonadFix (RWST r w s m) where
    mfix f = RWST $ \r s -> mfix $ \(a,_,_) -> runRWST (f a) r s

instance (Monoid w) => MonadTrans (RWST r w s) where
    lift m = RWST $ \_ s -> do
        a <- m
        return (a, s, mempty)

instance (Monoid w, MonadIO m) => MonadIO (RWST r w s m) where
    liftIO m = RWST $ \_ s -> do
        a <- liftIO m
        return (a, s, mempty) 

instance (Contravariant m) => Contravariant (RWST r w s m) where
    contramap f m = RWST $ \r s -> 
        contramap (\(a,s',w) -> (f a,s',w)) $ runRWST m r s

instance (Monoid w, Monad m) => MonadReader r (RWST r w s m) where
    ask   = RWST $ \r s -> return (r,s,mempty)
    local f m = RWST $ \r s -> runRWST m (f r) s
    reader f = f <$> ask

instance (Monoid w, Monad m) => MonadWriter w (RWST r w s m) where
    writer (a,w) = RWST $ \_ s -> return (a,s,w)
    tell w       = RWST $ \_ s -> return ((),s,w)
    listen m     = RWST $ \r s -> do
        (a,s',w) <- runRWST m r s
        return ((a,w),s',w)
    pass m       = RWST $ \r s -> do
        ((a,f),s',w) <- runRWST m r s
        return (a,s',f w)

instance (Monoid w, Monad m) => MonadState s (RWST r w s m) where
    state f = RWST $ \_ s -> let (a,s') = f s in return (a,s',mempty)
    get     = RWST $ \_ s -> return (s,s,mempty)
    put s   = RWST $ \_ _ -> return ((),s,mempty)

type M r w s m = ReaderT r (WriterT w (StateT s m))

fromRWST :: (Monad m) => RWST r w s m a -> M r w s m a
fromRWST m = ReaderT $ \r -> WriterT . StateT $ \s -> do
    (a,s',w) <- runRWST m r s
    return ((a,w),s')

toRWST :: (Monad m) => M r w s m a -> RWST r w s m a
toRWST m = RWST $ \r s -> do
    let m1      = runReaderT m r
    let m2      = runWriterT m1
    let m3      = runStateT m2 s
    ((a,w),s') <- m3
    return (a,s',w)
