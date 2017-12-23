{-# LANGUAGE 
    MultiParamTypeClasses,
    FunctionalDependencies,
    FlexibleInstances 
#-}

module  ReaderT 
    (   ReaderT     (..)
    )   where

import Control.Monad
import Control.Monad.Trans.Class

newtype ReaderT r m a = ReaderT { runReaderT :: r -> m a }


instance (Monad m) => Monad (ReaderT r m) where
    return a = ReaderT $ \_ -> return a
    m >>= k  = ReaderT $ \r -> do
        a <- runReaderT m r
        b <- runReaderT (k a) r
        return b


instance (Monad m) => Applicative (ReaderT r m) where
    pure  = return
    (<*>) = ap 

instance (Monad m) => Functor (ReaderT r m) where
    fmap f m = pure f <*> m

instance MonadTrans (ReaderT r) where
    lift m = ReaderT $ \_ -> m


class (Monad m) => MonadReader r m | m -> r where
    ask :: m r
    local :: (r -> r) -> m a -> m a

instance (Monad m) => MonadReader r (ReaderT r m)  where
    ask = ReaderT return
    local f m = ReaderT $ \r -> runReaderT m (f r)







