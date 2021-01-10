{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module  Store
    (   Store (..)
    ,   State (..)
    ,   listComponent 
    )   where

import Data.Tuple.Extra

import Control.Monad
import Control.Comonad
import Control.Monad.State.Class

import UI
import Pairing
import Console
import Component

data Store s a = Store (s -> a) s

instance Functor (Store s) where
  fmap f (Store g s) = Store (f . g) s

instance Comonad (Store s) where
  extract :: Store s a -> a                       -- Just a reminder 
  extract (Store f s) = f s
  duplicate :: Store s a -> Store s (Store s a)   -- Just a reminder 
  duplicate (Store f s) = Store (Store f) s

data State s a = State (s -> (a,s))

instance Functor (State s) where 
  fmap f (State g) = State $ (f *** id) . g

instance Applicative (State s) where
  pure   = return
  (<*>)  = ap

instance Monad (State s) where
  return a = State (a,)
  (State f) >>= g = State $ \s -> 
    let (a,s')     = f s 
        (State f') = g a 
    in f' s' 

instance MonadState s (State s) where
  get :: State s s
  get = State $ id &&& id

  put :: s -> State s ()
  put s = State $ const ((),s)

instance Pairing (State s) (Store s) where
  pair :: (a -> b -> c) -> State s a -> Store s b -> c
  pair op (State f) (Store g s) = let (a,s') = f s in op a (g s')

-- type Component base w m a = w (UI base m a)
-- base = IO            : base monad
-- w = Store [String]   : space comonad
-- m = State [String]   : action monad
-- a = Console
listComponent :: Component IO (Store [String]) (State [String]) Console
listComponent = Store render initStore where
    initStore :: [String]
    initStore = []

    -- type UI base action a = (action () -> base ()) -> a
    -- base = IO
    -- action = State [String]
    -- a = Console
    render :: [String] -> UI IO (State [String]) Console
    render _xs _send = Console
        { _text   = undefined
        , _action = undefined
        }

