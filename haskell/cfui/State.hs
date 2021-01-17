{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module  State
    (   State   (..)
    )   where

import Data.Tuple.Extra

import Control.Monad
import Control.Monad.State.Class

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


