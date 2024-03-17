{-# LANGUAGE GADTs  #-}

module Lang.Logger
  ( Logger 
  , LoggerF     (..)
  , LogLevel    (..)
  , Message     (..)
  , logMessage
  ) where

import Core.Free

data LoggerF next where
  LogMessage :: LogLevel -> Message -> (() -> next) -> LoggerF next

instance Functor LoggerF where
  fmap f (LogMessage lvl msg next) = LogMessage lvl msg (f . next)

instance Foldable LoggerF where
  foldMap f (LogMessage _ _ next) = f (next ())

instance Traversable LoggerF where
  traverse f (LogMessage lvl msg next) = LogMessage lvl msg <$> (const <$> f (next ()))

type Logger a = Free LoggerF a

data LogLevel = Info

newtype Message = Message { unMessage :: String }

logMessage :: LogLevel -> Message -> Logger ()
logMessage lvl msg = liftF $ LogMessage lvl msg id
