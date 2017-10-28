{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module  Reader
    (   Reader      (..)
    ,   asks
    )   where

import Control.Monad
import Control.Monad.Reader.Class hiding (asks)

newtype Reader r a = Reader { runReader :: r -> a } 


instance Functor (Reader r) where
    fmap f m = pure f <*> m


instance Applicative (Reader r) where
    pure  = return
    (<*>) = ap

instance Monad (Reader r) where
    return a = Reader $ \_ -> a 
    m >>= k  = Reader $ \r -> runReader (k $ runReader m r) r


instance MonadReader r (Reader r) where
    ask = Reader id
    local f m = Reader (runReader m . f)

asks :: (r -> a) -> Reader r a
asks = Reader

