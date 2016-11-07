{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module StateT 
  ( StateT 
  , state
  )
  where

import qualified Control.Monad.State.Class as CM

-- Attempting to guess what an implementation of StateT is

newtype StateT s m a = StateT { runStateT :: s -> m (a, s) }

-- hiding implementation detail
state :: Monad m => (s -> m (a, s)) -> StateT s m a
state = StateT

-- 'get' is meant to return the state of a state monad. In this case,
-- part of the 'state' is hidden in the monad 'm'. Hence, we can only
-- hope to retrieve a partial state, so to speak.

get :: Monad m =>  StateT s m s  
get = state $ \s -> return (s, s)



-- 'put' is meant to set the state of a state monad.
put :: Monad m => s -> StateT s m ()
put s = state $ \_ -> return ((), s) 



-- first things first, we need to have a monad
instance Monad m => Monad (StateT s m) where
  return a  = state $ \s -> return (a, s) 
  m >>= f   = state $ \s -> runStateT m s >>= \(a,t) -> runStateT (f a) t

class Monad m => MonadState s m where
  get' :: m s
  get'  = state' $ \s -> (s, s)  

  put' :: s -> m ()
  put' s = state' $ \_ -> ((), s)

  state' :: (s -> (a, s)) -> m a
  state' f = get' >>= \s -> (put'. snd . f) s >> ((return . fst . f) s)
{-
  state' f = do
    s <- get'
    let (a, s') = f s
    put' s'
    return a
-}


-- class default method implementations are circular
-- Need to overwrite state' or (get', put')
-- however, state and state' do not even have same type

instance Monad m => MonadState s (StateT s m) where
  get' = get 
  put' = put

-- so we have a state' implied by put and get, but it isnt 'state'
-- can we guess what this state' is really doing ?

state'' :: Monad m => (s -> (a, s)) -> StateT s m a
state'' f = state $ return . f

-- question : can we prove that state' = state''




instance Monad m => CM.MonadState s (StateT s m) where
  state = CM.state  -- unnecessary, class has a default 'state' implementation
  get   = CM.get
  put   = CM.put










