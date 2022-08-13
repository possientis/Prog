{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# OPTIONS_GHC -Wno-orphans        #-}

module Stitch.Control.Monad.HReader
  ( MonadHReader  (..)
  ) where 

import Control.Monad.Reader
import Data.Kind
import Text.Parsec.Prim

-- These orphan instances are necessary for the ParsecT instance below.
deriving instance Foldable Consumed
deriving instance Traversable Consumed


-- | Classifies a reader monad where a local computation can
-- change the type of the environment
class Monad m => MonadHReader r1 m | m -> r1 where
  -- | Update the environment to a new type
  type SetEnv r2 m :: Type -> Type

  -- | Compute with a local environment, possibly of a different
  -- type than the outer environment
  hlocal :: (r1 -> r2) -> (Monad (SetEnv r2 m) => SetEnv r2 m a) -> m a

instance Monad m => MonadHReader r1 (ReaderT r1 m) where
  type SetEnv r2 (ReaderT r1 m) = ReaderT r2 m
  hlocal f action = ReaderT $ runReaderT action . f

instance MonadHReader r1 m => MonadHReader r1 (ParsecT s u m) where
  type SetEnv r2 (ParsecT s u m) = ParsecT s u (SetEnv r2 m)
  hlocal f action = mkPT $ \s ->
    hlocal f $ traverse (fmap return) =<< runParsecT action s


