module  MonadReader
    (   Reader      (..)
    ,   ask
    ,   asks
    ,   local
    )   where

import Control.Monad

newtype Reader r a = Reader { runReader :: r -> a } 


instance Functor (Reader r) where
    fmap f m = pure f <*> m


instance Applicative (Reader r) where
    pure  = return
    (<*>) = ap

instance Monad (Reader r) where
    return a = Reader $ \_ -> a 
    m >>= k  = Reader $ \r -> runReader (k $ runReader m r) r



ask :: Reader r r
ask =  Reader id

asks :: (r -> a) -> Reader r a
asks =  Reader

local :: (r -> r) -> Reader r a -> Reader r a
local f m = Reader $ runReader m . f
