{-# LANGUAGE GADTs  #-}

module Lang.App
  ( App
  , AppF  (..)
  , evalLogger
  ) where

import Core.Free
import Lang.Logger

data AppF next where
  EvalLogger :: Logger () -> (() -> next) -> AppF next

instance Functor AppF where
  fmap f (EvalLogger logAct next) = EvalLogger logAct (f . next)

instance Foldable AppF where
  foldMap f (EvalLogger _ next) = f (next ())

instance Traversable AppF where
  traverse f (EvalLogger logAct next) = EvalLogger logAct <$> (const <$> f (next ()))

type App a = Free AppF a

evalLogger :: Logger () -> App ()
evalLogger logAct = liftF $ EvalLogger logAct id 

